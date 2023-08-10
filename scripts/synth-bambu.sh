#!/usr/bin/env bash

set -x

scriptsdir=$(dirname "$(readlink -f "$BASH_SOURCE")")

if [[ -z "$1" ]]; then
    parallel=1
else
    parallel=$1
fi

if [[ -z "$2" ]]; then
    output=$(pwd)
else
    output=$2
fi

if [[ -z "$3" ]]; then
    source=$(pwd)
else
    source=$3
fi

echo "copying directory structure from $source to $output"
mkdir -p $output
rsync -am --include '*/' --include '*.v' --exclude '*' $source/ $output/

echo "executing $parallel runs in parallel"
cat ./benchmark-list-master | \
    xargs --max-procs=$parallel --replace=% \
    $scriptsdir/synth-ssh-bambu.sh 0 % $output
