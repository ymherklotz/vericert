#!/usr/bin/env bash

top=$(pwd)
vericert=/vericert
rm $top/exec_legup.csv
legup_dir=/data/legup-polybench-$1/legup/legup_$2

while read benchmark ; do
    cd $legup_dir/$benchmark
    iverilog -o run -s main_tb $vericert/ip/* legup.v
    cycles=$(./run | sed -n 3p | sed -E -e 's/[^0-9]+([0-9]+)/\1/')
    echo "$(basename "$benchmark"),$cycles" >>$top/exec_legup.csv
done < benchmark-list-master
