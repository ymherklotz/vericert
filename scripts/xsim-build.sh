#!/usr/bin/bash

set -e

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

export PATH=/opt/vitis/Vivado/2023.2/bin:$PATH
export LD_LIBRARY_PATH=/opt/vitis/Vivado/2023.2/lib/lnx64.o:$LD_LIBRARY_PATH

xvhdl $SCRIPT_DIR/../ip/float/float.vhd
xvlog -sv $1

xelab testbench -L unisims_ver -L unimacro_ver -L xilinxcorelib_ver -L secureip -L xpm

xsim --runall work.testbench
