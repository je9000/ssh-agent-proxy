#!/usr/local/bin/perl

use 5.008;
use warnings;
use strict;
use IO::Socket::UNIX;
use IO::Select;
use POSIX qw( setsid );
use File::Temp qw( tempdir );

# Debugging
use constant DEBUG   => 0;
use constant NO_FORK => 0;

# Configurable constants
use constant MAX_AGENT_SEARCHES            => 2;
use constant SSH_AGENT_VALIDATION_TIMEOUT  => 5;
use constant SCREEN_PROCESS_CHECK_INTERVAL => 600;

# Directory/filename configurations
use constant SSH_AUTH_SOCKETS_SEARCH_DIR   => '/tmp/';                              # Wants the trailing slash
use constant AUTH_SOCKETS_DIR_MATCH_REGEX  => qr/^ssh-/;
use constant AUTH_SOCKETS_FILE_MATCH_REGEX => qr/^agent\.\d+$/;
use constant MY_SOCKET_DIR_TEMPLATE        => 'ssh-proxy-XXXXXXXXXX';
use constant MY_SCREEN_SOCKET_FILE_MATCH_REGEX => qr/^\d+\..+/;

# Trailing slash needed
my $MY_SCREEN_SOCKET_DIR;
if ( $^O eq 'freebsd' ) {
    $MY_SCREEN_SOCKET_DIR = '/tmp/screens/S-' . getlogin() . '/';
} elsif ( $^O eq 'linux' ) {
    $MY_SCREEN_SOCKET_DIR = '/var/run/screen/S-' . getlogin() . '/';
} else {
    die "I don't know where to find your screen socket directory!";
}

# Internal constants
use constant SOCKET_TYPE_NONE                          => 0;
use constant SOCKET_TYPE_CLIENT                        => 1;
use constant SOCKET_TYPE_AGENT                         => 2;
use constant PAIR_TYPE                                 => 0;
use constant PAIR_SOCKET                               => 1;
use constant PAIR_AGENT_INFO                           => 2;
use constant STAT_MTIME                                => 9;
use constant SSH_MESSAGE_AGENTC_REQUEST_RSA_IDENTITIES => "\x00\x00\x00\x01\x01";
use constant SSH2_MESSAGE_AGENTC_REQUEST_IDENTITIES    => "\x00\x00\x00\x01\x0B";

if ( DEBUG ) {
    require Data::Hexdumper;
    import Data::Hexdumper( 'hexdump' );
    require Data::Dumper;
    import Data::Dumper;
}

# These are a 1-byte message containing SSH_AGENT_FAILURE, SSH2_AGENT_FAILURE, SSH_COM_AGENT2_FAILURE
my %is_SSH_AGENT_FAILURE =
 ( "\x00\x00\x00\x01\x05" => 1, "\x00\x00\x00\x01\x1E" => 1, "\x00\x00\x00\x01\x66" => 1 );

my %SSH_REPLY_CODE_FOR = (
    &SSH_MESSAGE_AGENTC_REQUEST_RSA_IDENTITIES    => 0x02,
    &SSH2_MESSAGE_AGENTC_REQUEST_IDENTITIES => 0x0C,
);

# Default to use current environment's AUTH_SOCK. Won't always work, but worth a try.
my $last_ssh_auth_sock = defined $ENV{SSH_AUTH_SOCK} ? $ENV{SSH_AUTH_SOCK} : '';
my %socket_pairs;
my %bad_sockets;    # Paths to "bad" sockets with the mtime for that socket.
my $select;
my %options;
my ( $socket_path, $socket_dir ) = make_temp_socket();

sub debug_print ($) {
    return unless DEBUG;
    my $fh;
    my $old_umask = umask(0177);
    my $t = scalar(localtime(time()));
    $t =~ s/^.+? //;
    open( $fh, ">>/tmp/proxy-log" );
    print $fh "$t: $_[0]\n";
    close( $fh );
}

sub die_usage {
    die <<'USAGE';
Usage:
    -c    Generate csh-style shell syntax
    -s    Generate sh-style shell syntax
    -p    Generate only the proxy socket path
    -e    Exit when all of your screen sessions exit
    -i    Insecure mode. Does not require connected clients and agents to be
          running under same euid. Removes the dependency on BSD::getpeereid.

USAGE
}

sub make_temp_socket {
    my $tdir = tempdir( MY_SOCKET_DIR_TEMPLATE, TMPDIR => 1 );
    if ( !$tdir ) { die "Unable to create temporary directory!"; }
    if ( -e "$tdir/proxy.$$" ) { die "Unable to create temporary filename!"; }
    return ( "$tdir/proxy.$$", $tdir );
}

sub daemonize {
    POSIX::setsid();
    chdir( "/" );
    close( STDERR );
    close( STDOUT );
    close( STDIN );
}

sub exit_cleanup {
    my ( $exit ) = @_;
    if ( DEBUG ) {
        my $call_stack = '';
        my $x = 0;
        while ( my @caller = caller($x++) ) {
            $caller[6] =~ s/[\n\t ]+/ /g;
            $call_stack .= "\n line: $caller[2], sub: $caller[3] ($caller[6])";
        }
        $exit = 'not defined' if !defined $exit;
        debug_print "exit_cleanup:$exit" . $call_stack;
    }
    if ( $socket_path ) { unlink $socket_path; undef $socket_path; }
    if ( $socket_dir )  { rmdir $socket_dir;   undef $socket_dir; }
    exit if defined $exit;
}

sub scan_for_authsocks {
    my $dirh;
    my @potential_dirs;
    my @potential_sockets;

    # Clear out the old bad sockets
    foreach my $s ( keys( %bad_sockets ) ) {
        delete $bad_sockets{$s} unless ( ( -S $s ) && ( ( stat( $s ) )[STAT_MTIME] == $bad_sockets{$s} ) );
    }

    opendir( $dirh, SSH_AUTH_SOCKETS_SEARCH_DIR ) or return;

    # That's "directory entry".
    while ( my $dire = readdir( $dirh ) ) {
        next if ( $dire eq '.' || $dire eq '..' );
        debug_print "scanning $dire";
        next unless $dire =~ AUTH_SOCKETS_DIR_MATCH_REGEX;
        debug_print "passed regex $dire";
        $dire = SSH_AUTH_SOCKETS_SEARCH_DIR . $dire;
        next unless -d $dire && -o $dire;
        debug_print "passed stat1 $dire";

        # Test that the dir is chmod 0700.
        next unless ( ( ( stat( $dire ) )[2] & 0700 ) == 0700 );
        if ( $dire !~ m#/$# ) { $dire .= '/'; }
        debug_print "looks good, saving $dire";
        push @potential_dirs, $dire;
    }
    closedir( $dirh );

    foreach my $dir ( @potential_dirs ) {
        opendir( $dirh, $dir ) or next;
        while ( my $dire = readdir( $dirh ) ) {
            next if ( $dire eq '.' || $dire eq '..' );
            debug_print "scanning file $dire";

            # Normal ssh-agent and ssh -A connections put the PID of the agent
            # in the filename. If we found it (based on the constant regex),
            # we can test it later to make sure the target PID is valid.
            next unless $dire =~ AUTH_SOCKETS_FILE_MATCH_REGEX;
            debug_print "passed regex $dire";
            my $matched_pid = $1;
            $dire = $dir . $dire;
            next unless -S $dire && -o $dire && -w $dire;
            debug_print "passed stat check $dire";
            if ( exists $bad_sockets{$dire} && $bad_sockets{$dire} == ( stat( $dire ) )[STAT_MTIME] ) {
                next;
            }
            debug_print "passed bad socket check $dire";

            # Return the first one we find.
            push @potential_sockets, $dire;
        }
        closedir( $dirh );
    }
    return @potential_sockets;
}

sub close_paired_socket {
    my ( $socket ) = @_;
    debug_print "Closing paired socket $socket";
    $select->remove( $socket );
    $socket->close();
    my $other_end = $socket_pairs{$socket}->[PAIR_SOCKET];
    if ( $other_end ) {
        debug_print "Closing other end $other_end:";
        $socket_pairs{$other_end}->[PAIR_SOCKET] = undef;
    }
    delete $socket_pairs{$socket};
}

sub close_socket_pair {
    my ( $close_me ) = @_;
    my $other_info = $socket_pairs{$close_me};
    if ( $other_info ) {
        my $other_end = $other_info->[PAIR_SOCKET];
        close_paired_socket( $other_end );
    }
    close_paired_socket( $close_me );
}

sub store_socket_pair {
    my ( $to_client, $to_agent, $agent_info ) = @_;

    die "Stupid programmer!" unless $to_client && $to_agent;
    $socket_pairs{$to_client} = [SOCKET_TYPE_AGENT, $to_agent, $agent_info];
    $socket_pairs{$to_agent} = [SOCKET_TYPE_CLIENT, $to_client];
    if ( DEBUG ) {
        debug_print "Storing socket pair: to_client => $to_client, to_agent => $to_agent\n " . Dumper(\%socket_pairs);
    }
    $select->add( $to_client, $to_agent );
}

sub decode_identity_reply {
    my ( $buf, $expected_code ) = @_;

    if ( length( $buf ) < 9 ) { return undef; }
    my ( $length, $code, $id_count ) = unpack( 'NUN', $buf );
    debug_print "decoded this: $length, $code, $id_count";
    if ( $code ne $expected_code ) { return undef; }
    return ( $id_count, $length );
}

# Returns weighted number representing how "good" this socket is and the socket itself.
# Weight is based on how many keys are loaded + 1 if the socket is connected to a live
# agent. Thus, if the agent is not "live", 0 is returned. Takes a socket file and the
# current best weight as arguments -- if our weight is not > the best weight, we don't
# return the current socket handle. This way we only maintain an open connection to the
# current "best" socket.
sub test_authsock {
    my ( $agent_socket_file, $best_weight ) = @_;

    die "Stupid programmer!" unless $agent_socket_file;
    my $agent_sock = IO::Socket::UNIX->new(
        Type => SOCK_STREAM,
        Peer => $agent_socket_file,
    );
    if ( !$agent_sock ) {
        debug_print "connection failed";
        return 0;
    }
    debug_print "client_sock is $agent_sock and is connceted to $agent_socket_file";
    if ( !$options{insecure} ) {
        my ( $remote_uid, $remote_gid ) = getpeereid( $agent_sock->fileno );
        if ( !defined $remote_uid ) {
            debug_print "getpeereid failed -- refusing to run insecure";
            $agent_sock->close();
            exit_cleanup( 'problem with getpeereid' );
        }
        if ( $remote_uid != $> ) {
            debug_print "Rejecting ssh agent, wrong euid";
            $agent_sock->close();
            return 0;
        }
    }
    debug_print "connected to server, sending test query";
    my ( $buf, $identity_count, $message_length );
    my $total_keys_loaded = 0;

    # We jack with alarm() here, so make sure we reset it before exiting.
    $agent_sock->send( SSH_MESSAGE_AGENTC_REQUEST_RSA_IDENTITIES );
    eval {
        local $SIG{ALRM} = sub { die "a\n"; };
        local $SIG{__DIE__} = undef;
        alarm SSH_AGENT_VALIDATION_TIMEOUT;
        $agent_sock->recv( $buf, 1024 );
        ( $identity_count, $message_length ) = decode_identity_reply( $buf, $SSH_REPLY_CODE_FOR{&SSH_MESSAGE_AGENTC_REQUEST_RSA_IDENTITIES} );
        debug_print "after decode, id is " . ( defined $identity_count ? 'defined' : 'undefined' );
        if ( !defined $identity_count ) { die "i\n"; }
        debug_print "message length is $message_length, buf is " . length($buf);
        $message_length -= ( length($buf) - 4 );
        while ( $message_length > 0 ) {
            debug_print "Reading remaining $message_length bytes";
            my $buf2;
            $agent_sock->recv( $buf2, 1024 );
            die "e\n" if ( length( $buf2 ) < 1 );
            $message_length -= length($buf2);
        }
        alarm 0;
    };
    if ( $@ ) {
        debug_print "got error $@";
        alarm 0;
        $agent_sock->close();
        debug_print "Got a bad SSH_MESSAGE_AGENTC_REQUEST_RSA_IDENTITIES result";
        $bad_sockets{$agent_socket_file} = ( stat( $agent_socket_file ) )[STAT_MTIME];
        alarm SCREEN_PROCESS_CHECK_INTERVAL if $options{exit_with_screen};
        return 0;
    }
    if ( $buf ) { debug_print "ident reply!"; }
    #if ( $buf ) { debug_print "ident reply: " . hexdump( data => $buf ); }
    debug_print "got reply, saw $identity_count keys";
    $total_keys_loaded += $identity_count;

    $agent_sock->send( SSH2_MESSAGE_AGENTC_REQUEST_IDENTITIES );
    eval {
        local $SIG{ALRM} = sub { die "a\n"; };
        local $SIG{__DIE__} = undef;
        alarm SSH_AGENT_VALIDATION_TIMEOUT;
        $agent_sock->recv( $buf, 1024 );
        ( $identity_count, $message_length ) = decode_identity_reply( $buf, $SSH_REPLY_CODE_FOR{&SSH2_MESSAGE_AGENTC_REQUEST_IDENTITIES} );
        debug_print "after decode, id is " . ( defined $identity_count ? 'defined' : 'undefined' );
        if ( !defined $identity_count ) { die "i\n"; }
        debug_print "message length is $message_length, buf is " . length($buf);
        $message_length -= ( length($buf) - 4 );
        debug_print "before loop";
        while ( $message_length > 0 ) {
            debug_print "Reading remaining $message_length bytes";
            my $buf2;
            $agent_sock->recv( $buf2, 1024 );
            die "e\n" if ( length( $buf2 ) < 1 );
            $message_length -= length($buf2);
        }
        alarm 0;
    };
    if ( $@ ) {
        debug_print "got error $@";
        alarm 0;
        $agent_sock->close();
        debug_print "Got a bad SSH2_MESSAGE_AGENTC_REQUEST_IDENTITIES result";
        $bad_sockets{$agent_socket_file} = ( stat( $agent_socket_file ) )[STAT_MTIME];
        alarm SCREEN_PROCESS_CHECK_INTERVAL if $options{exit_with_screen};
        return 0;
    }
    if ( $buf ) { debug_print "ident reply!"; }
    #if ( $buf ) { debug_print "ident reply: " . hexdump( data => $buf ); }
    debug_print "got reply, decoded $identity_count keys";
    alarm SCREEN_PROCESS_CHECK_INTERVAL if $options{exit_with_screen};
    # Extra +1 bonus for being a "live" socket.
    $total_keys_loaded += $identity_count + 1;

    if ( $total_keys_loaded > $best_weight ) {
        return ( $total_keys_loaded, $agent_sock );
    } else {
        $agent_sock->close();
        return ( $total_keys_loaded, undef );
    }
}

sub connect_to_best_agent {
    my ( $to_client ) = @_;
    my $best_weight = 0;
    my $best_socket_file;
    my $best_socket_handle;

    die "Stupid programmer!" unless $to_client;
    debug_print "entered connect_to_best_agent";
    my @auth_socks = scan_for_authsocks();
    debug_print "Possible agents: " . join(', ', @auth_socks);
    foreach my $sock ( @auth_socks ) {
        my ( $weight, $socket ) = test_authsock( $sock, $best_weight );
        debug_print "weight for $sock is $weight";
        if ( $weight > $best_weight ) {
            debug_print "$sock is the best so far!";
            $best_weight        = $weight;
            $best_socket_file   = $sock;
            $best_socket_handle = $socket;
        }
    }
    return 0 unless $best_weight;
    store_socket_pair(
        $to_client,
        $best_socket_handle,
        {
            AGENT_PATH       => $best_socket_file,
            AGENT_PATH_MTIME => ( stat( $best_socket_file ) )[STAT_MTIME]
        }
    );
    return 1;
}

sub connect_to_agent {
    my ( $to_client ) = @_;
    my $agent_searches = 0;

    die "Stupid programmer!" unless $to_client;
    debug_print "entered connect_to_agent";
    if ( $last_ssh_auth_sock ) {
        my ( undef, $to_agent ) = test_authsock( $last_ssh_auth_sock, 0 );
        if ( $to_agent ) {
            debug_print "connected to last_ssh_auth_sock!";
            store_socket_pair(
                $to_client,
                $to_agent,
                {
                    AGENT_PATH       => $last_ssh_auth_sock,
                    AGENT_PATH_MTIME => ( stat( $last_ssh_auth_sock ) )[STAT_MTIME]
                }
            );
            return 1;
        }
    }

    while ( $agent_searches < MAX_AGENT_SEARCHES ) {
        $agent_searches++;
        debug_print "trying to connect to best agent...";
        if ( connect_to_best_agent($to_client) ) {
            debug_print "connected to best agent!";
            return 1;
        }
    }
    debug_print "out of tries, unable to connect!";
    return 0;
}

# Adds a socket to the bad_sockets list based on its filename. Also unsets
# the $last_ssh_auth_sock if it matches the socket to be blacklisted.
sub blacklist_agent_socket {
    my ( $agent_socket ) = @_;
    my $our_auth_info = $socket_pairs{ $socket_pairs{$agent_socket}->[PAIR_SOCKET] }->[PAIR_AGENT_INFO];
    debug_print "blacklisting $our_auth_info->{AGENT_PATH}\@$our_auth_info->{AGENT_PATH_MTIME}";
    $bad_sockets{ $our_auth_info->{AGENT_PATH} } = $our_auth_info->{AGENT_PATH_MTIME};
    if ( $last_ssh_auth_sock eq $our_auth_info->{AGENT_PATH} ) { undef $last_ssh_auth_sock; }
}

sub is_my_screen_process_running {
    my $dirh;
    debug_print "scanning " . $MY_SCREEN_SOCKET_DIR . " for running screen processes";
    return 0 unless -o $MY_SCREEN_SOCKET_DIR;
    debug_print "dir ownership check passed";
    return 0 unless ( ( ( stat( $MY_SCREEN_SOCKET_DIR ) )[2] & 0700 ) == 0700 );
    debug_print "dir permissions check passed";
    opendir( $dirh, $MY_SCREEN_SOCKET_DIR ) or return 0;

    # That's "directory entry".
    while ( my $dire = readdir( $dirh ) ) {
        next if ( $dire eq '.' || $dire eq '..' );
        debug_print "scanning $dire";
        next unless $dire =~ MY_SCREEN_SOCKET_FILE_MATCH_REGEX;
        debug_print "socket file name match passed";
        $dire = $MY_SCREEN_SOCKET_DIR . $dire;
        next unless -o $dire && -r _ && -w _ && ( -S _ || -p _ );
        debug_print "socket file type, ownership, and permission check passed";
        debug_print "found a screen!";
        return 1;
    }
    closedir( $dirh );
    debug_print "no screens found!";
    return 0;
}

while ( @ARGV ) {
    my $arg = $ARGV[0];
    if ( $arg !~ /^-/ ) { last; }
    elsif ( $arg eq '-c' ) { $options{gen_csh}          = 1; shift( @ARGV ); }
    elsif ( $arg eq '-s' ) { $options{gen_sh}           = 1; shift( @ARGV ); }
    elsif ( $arg eq '-p' ) { $options{gen_socket}       = 1; shift( @ARGV ); }
    elsif ( $arg eq '-e' ) { $options{exit_with_screen} = 1; shift( @ARGV ); }
    elsif ( $arg eq '-i' ) { $options{insecure}         = 1; shift( @ARGV ); }
    else { print STDERR "Unknown flag '$arg', aborting.\n"; die_usage(); }
}
if ( !$options{insecure} ) {
    eval { require BSD::getpeereid; };
    if ( $@ ) {
        die
         "Failed to load BSD::getpeereid. Please make sure BSD::getpeereid is installed correctly or considure running in insecure mode.\n\n$@\n";
    }
    import BSD::getpeereid;
}

my $server_sock = IO::Socket::UNIX->new(
    Type   => SOCK_STREAM,
    Local  => $socket_path,
    Listen => 1
);
die "Failed to create server socket: $!" unless $server_sock;

if ( !NO_FORK ) {
    if ( my $child = fork() ) {
        close( $server_sock );
        if ( $options{gen_csh} && $options{gen_sh} ) { die_usage(); }
        if ( @ARGV ) {
            $ENV{SSH_AUTH_SOCK} = $socket_path;
            $ENV{SSH_AGENT_PID} = $child;
            exec { $ARGV[0] } ( @ARGV );
            exit( 1 );
        }
        if ( $options{gen_socket} ) {
            print "$socket_path\n";
        } else {
            if ( !$options{gen_sh} && $ENV{SHELL} =~ /csh$/ ) {
                print
                 "setenv SSH_AUTH_SOCK $socket_path;\nsetenv SSH_AGENT_PID $child;\necho Agent pid $child;\n";
            } else {
                print "SSH_AUTH_SOCK=$socket_path;\nSSH_AGENT_PID=$child;\necho Agent pid $child;\n";
            }
        }
        exit;
    }
    daemonize();
}

$SIG{INT}     = sub { exit_cleanup( 'int' ); };
$SIG{TERM}    = sub { exit_cleanup( 'term' ); };
$SIG{KILL}    = sub { exit_cleanup( 'kill' ); };
$SIG{__DIE__} = sub { exit_cleanup( undef ); debug_print "Die handler called! $_[0]"; exit( 3 ); };

if ( $options{exit_with_screen} ) {
    $SIG{ALRM} = sub {
        if ( !is_my_screen_process_running() ) { exit_cleanup( 'exit_with_screen' ); }
        alarm SCREEN_PROCESS_CHECK_INTERVAL;
    };
    alarm SCREEN_PROCESS_CHECK_INTERVAL;
}

debug_print( "\n" x 50 ) . "starting up: " . scalar( localtime() );
$select = IO::Select->new();
$select->add( $server_sock );
while ( 1 ) {
    while ( my @ready = $select->can_read() ) {
        foreach my $ready_to_read ( @ready ) {
            if ( $ready_to_read == $server_sock ) {
                my $server_sock_to_client = $server_sock->accept();
                debug_print "accepted!";

                if ( !$options{insecure} ) {
                    my ( $remote_uid, $remote_gid ) = getpeereid( $server_sock_to_client->fileno );
                    if ( !defined $remote_uid ) {
                        debug_print "getpeereid failed -- refusing to run insecure";
                        exit_cleanup( 'getpeereid failed' );
                    }

                    # Check that the remote user is running under the same EUID that we are.
                    if ( $remote_uid != $> ) {
                        debug_print "rejecting connection from $remote_uid";
                        $server_sock_to_client->close();
                        next;
                    }
                }
                if ( !connect_to_agent( $server_sock_to_client ) ) {
                    debug_print "connect_to_agent failed! aborting";
                    $server_sock_to_client->close();
                    next;
                }
                debug_print
                 "connected socket pair, client:$server_sock_to_client server:$socket_pairs{$server_sock_to_client}->[PAIR_SOCKET]";
            } else {
                my $buf;
                my $r = sysread( $ready_to_read, $buf, 1024 );
                debug_print "read $r bytes from $ready_to_read";
                if ( !$r ) {
                    # One end closed the connection, clean up
                    debug_print "socket error! $!";
                    close_socket_pair( $ready_to_read );
                    next;
                } else {
                    #debug_print hexdump( data => $buf );
                }
                my ( $other_end_type, $other_end ) = @{ $socket_pairs{$ready_to_read} };
                if (   ( $other_end_type == SOCKET_TYPE_CLIENT )
                    && ( length( $buf ) == 5 )
                    && ( $is_SSH_AGENT_FAILURE{$buf} ) )
                {
                    debug_print "got SSH2?_AGENT_FAILURE";
                    # Blacklist BEFORE you close because we need that reverse
                    # mapping!
                    # Not sure we want to do this, since it should happen for
                    # us when our client sees the bad data and disconnectes.
                    # On reconnection, the regular socket testing code would
                    # blacklist this socket for us. Same for the blacklisting
                    # that happens below (in the write failure code).
                    blacklist_agent_socket( $ready_to_read );
                    close_socket_pair( $ready_to_read );
                    next;
                }
                if ( !defined syswrite( $other_end, $buf, length( $buf ) ) ) {
                    debug_print "write failed to $other_end";
                    blacklist_agent_socket( $ready_to_read );
                    close_socket_pair( $ready_to_read );
                    #implicit next;
                }
            }
        }
    }
    sleep 1;
}

exit_cleanup( 'program end' );
# We're done!
