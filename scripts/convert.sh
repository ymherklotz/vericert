file=$1
benchmark=$(echo $1 | sed 's:.*/\([^/]\+\)/encode_report.xml:\1:')

lut_flip_flop=$(sed -n "s/.*XILINX_LUT_FLIP_FLOP_PAIRS_USED.*\"\([0-9.]*\)\".*/\1/p" $file)
slice=$(sed -n "s/.*XILINX_SLICE\".*\"\([0-9.]*\)\".*/\1/p" $file)
regs=$(sed -n "s/.*XILINX_SLICE_REGISTERS.*\"\([0-9.]*\)\".*/\1/p" $file)
luts=$(sed -n "s/.*XILINX_SLICE_LUTS.*\"\([0-9.]*\)\".*/\1/p" $file)
ramfifo=$(sed -n "s/.*XILINX_BLOCK_RAMFIFO.*\"\([0-9.]*\)\".*/\1/p" $file)
iopin=$(sed -n "s/.*XILINX_IOPIN.*\"\([0-9.]*\)\".*/\1/p" $file)
dsps=$(sed -n "s/.*XILINX_DSPS.*\"\([0-9.]*\)\".*/\1/p" $file)
power=$(sed -n "s/.*XILINX_POWER.*\"\([0-9.]*\)\".*/\1/p" $file)
delay=$(sed -n "s/.*XILINX_DESIGN_DELAY.*\"\([0-9.]*\)\".*/\1/p" $file)

echo $benchmark,$lut_flip_flop,$slice,$regs,$luts,$ramfifo,$iopin,$dsps,$power,$delay >>synth.csv
