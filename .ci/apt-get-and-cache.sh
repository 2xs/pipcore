#!/bin/bash

# "apt update ; apt install", with caching of the downloaded packages
# and current state, to minimise load on debian mirrors without having
# to build a new docker image

CACHE=.ci/apt-cached-state.tar.xz
CACHEVERSION=.ci/apt-cache-version

if [ -z "$1" ]; then
    printf 'Usage: %s <package>...\n' "$0"
    exit 1
fi

# Remove the configuration that disables apt cache if it exists
sudo rm -f /etc/apt/apt.conf.d/docker-clean

if cmp -s $CACHEVERSION $CACHEVERSION.cached; then
    printf 'Restoring APT cache (we assume no update and download are necessary)\n'
    sudo tar xvaf $CACHE -C /var
else
    printf 'APT cache absent or obsolete, starting from scratch\n'
    sudo apt update -y -q
fi

# first only download the packages, so that they end up in the cache
sudo DEBIAN_FRONTEND=noninteractive apt install -yqd "$@"
sudo tar caf $CACHE -C /var lib/apt cache/apt
printf 'Caching APT state: '
ls -sh $CACHE
cp $CACHEVERSION $CACHEVERSION.cached

# now really install the packages
sudo DEBIAN_FRONTEND=noninteractive apt install -yq --no-download "$@"
