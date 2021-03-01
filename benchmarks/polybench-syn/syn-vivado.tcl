create_project -in_memory -part xc7k70t
read_verilog top.v
synth_design -part xc7k70t -top main
create_clock -name clk -period 5.000 [get_ports clk]
report_timing -nworst 1 -path_type full -input_pins -file worst_timing.txt
write_verilog -force out.v
