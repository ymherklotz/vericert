#!/bin/bash

benchmark=./$1/$2
echo $benchmark

    cp ./synth.tcl $benchmark/. 2>/dev/null
    cd $benchmark || exit 1
    vivado -mode batch -source synth.tcl >vivado.log 2>&1
