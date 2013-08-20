#!/bin/sh
#export PATH=${PATH}:/home/john/bin

which screen > /dev/null
if [ $? -ne 0 ]; then
    echo Unable to locate screen, aborting.
    exit
fi

if [ -z "$SSH_AGENT_PROXY_SOCKET" ]; then
    export SSH_AGENT_PROXY_SOCKET=`ssh-agent-proxy.pl -p -e`
    if [ $? -ne 0 ]; then
        echo Error starting ssh-agent-proxy.pl, aborting.
        exit
    fi
    if [ "$SSH_AGENT_PROXY_SOCKET" ]; then
        exec ssh-agent $0 $*
    fi
else
    export SSH_AUTH_SOCK=$SSH_AGENT_PROXY_SOCKET
    exec screen $*
fi
