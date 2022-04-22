#!/bin/bash

# "apt update ; apt install", but from the local mirror

sudo cp .ci/sources.list /etc/apt/sources.list
sudo apt update -yq
sudo DEBIAN_FRONTEND=noninteractive apt install -yq --no-install-recommends "$@"
