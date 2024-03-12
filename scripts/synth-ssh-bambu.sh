#!/usr/bin/env bash

# Assumes that the Verilog is passed on the command line, that the tcl file is in synth.tcl and
# returns encode_report.xml.

scriptsdir=$(dirname "$(readlink -f "$BASH_SOURCE")")

num=$1
bench=$2
output=$3
machine=$VERICERT_MACHINE
user=$VERICERT_USER
files="$scriptsdir/synth-bambu.tcl $output/$bench/main_top.v"
log="$output/${bench}_synth.log"

date >$log

temp=$(ssh $user@$machine "mktemp -d")

>&2 echo "synthesising $bench $temp"
rsync $files $user@$machine:$temp/ >>$log 2>&1
ssh $user@$machine \
    "bash -lc 'cd $temp && vivado -mode batch -source synth-bambu.tcl'" \
    >>$log 2>&1
rsync $user@$machine:$temp/encode_report.xml $output/${bench}_report.xml >>$log 2>&1
# ssh $user@$machine "rm -rf '$temp'" >>$log 2>&1
rm -f main.sv >>$log 2>&1
>&2 echo "done $bench"
