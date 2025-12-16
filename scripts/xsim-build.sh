#!/usr/bin/bash

set -e

export PATH=/opt/vitis/Vivado/2023.2/bin:$PATH

xvhdl /home/ymh/projects/vericert/ip/float/float.vhd
xvlog -sv $1

xelab testbench -L unisims_ver -L unimacro_ver -L xilinxcorelib_ver -L secureip -L xpm

xsim --runall work.testbench
