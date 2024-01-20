#!/usr/bin/env bash

set -x

scriptsdir=$(dirname "$(readlink -f "$BASH_SOURCE")")

if [[ -z "$1" ]]; then
    parallel=1
else
    parallel=$1
fi

if [[ -z "$3" ]]; then
    output=$(pwd)
else
    output=$3
fi

if [[ -z "$2" ]]; then
    source=$(pwd)
else
    source=$2
fi

echo "copying directory structure from $source to $output"
mkdir -p $output
rsync -am --include '*/' --include '*.sv' --exclude '*' $source/ $output/
cp $source/benchmark-list-master $output/.
cp $source/exec.csv $output/.

echo "executing $parallel runs in parallel"
cd $output
cat ./benchmark-list-master | \
    xargs --max-procs=$parallel --replace=% \
    $scriptsdir/synth-ssh.sh 0 % .
