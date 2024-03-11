#!/usr/bin/env bash

opt=$1
bench=$2
base=$(pwd)
path=$(dirname $bench)
name=$(basename $bench)

cd $path

mkdir $name
cp $name.c $name/.
cd $name

sed -i 's/main/main_top/' $name.c
sed -i 's:include/misc.h:../include/misc.h:' $name.c

if [[ "$opt" = "opt" ]]; then
    bambu --simulate --top-fname=main_top $name.c 2>/dev/null
else
    bambu -fno-if-conversion -O0 --do-not-chain-memories --do-not-use-asynchronous-memories --clock-period=10 --top-fname=main_top --no-chaining --simulate $name.c 2>/dev/null
fi

cycles=$(./simulate_main_top.sh | sed -n -E -e 's/^.*\s+([0-9]+)\s+cycles.*$/\1/ p')

echo $name,$cycles >>$base/exec.csv

cd $base
