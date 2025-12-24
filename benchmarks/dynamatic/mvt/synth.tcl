# create_project -in_memory -part xc7z020clg484-1 -force

read_vhdl -vhdl2008 ../../../ip/float/float.vhd

read_verilog -sv mvt.sv

source ../../../ip/float/gen-fmul.tcl
source ../../../ip/float/gen-fadd.tcl

synth_design -top main -part xc7k160tfbg484-1 -no_iobuf -mode out_of_context

create_clock -name clk -period 4.000 -waveform {0.000 2.000} [get_ports clk]
set_property HD.CLK_SRC BUFGCTRL_X0Y0 [get_ports clk]

report_utilization > utilization_post_syn.rpt
report_timing > timing_post_syn.rpt
opt_design
place_design
route_design
report_utilization > utilization_post_pr.rpt
report_timing > timing_post_pr.rpt


close_design
close_project
