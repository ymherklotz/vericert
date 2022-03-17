#!/usr/bin/bash

# Assumes that the Verilog is passed on the command line, that the tcl file is in synth.tcl and
# returns encode_report.xml.

scriptsdir=$(dirname "$(readlink -f "$BASH_SOURCE")")

bench=$1
output=$2
machine=ee-beholder0.ee.ic.ac.uk
user=ymh15
files="$scriptsdir/synth.tcl $output/$bench.v"
log="$output/${bench}_synth.log"

date >$log

temp=$(ssh $user@$machine "mktemp -d" 2>>$log)

>&2 echo "synthesising $bench $temp"
rsync $files $user@$machine:$temp/ >>$log 2>&1
ssh $user@$machine \
    "bash -lc 'cd $temp && cp $(basename $bench).v main.v && vivado -mode batch -source synth.tcl'" \
    >>$log 2>&1
rsync $user@$machine:$temp/encode_report.xml $output/${bench}_report.xml >>$log 2>&1
ssh $user@$machine "rm -rf '$temp'" >>$log 2>&1
rm -f main.v >>$log 2>&1
>&2 echo "done $bench"
