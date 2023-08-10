proc dump_statistics {  } {
  set util_rpt [report_utilization -return_string]
  set LUTFFPairs 0
  set SliceRegisters 0
  set Slice 0
  set SliceLUTs 0
  set SliceLUTs1 0
  set BRAMFIFO36 0
  set BRAMFIFO18 0
  set BRAMFIFO36_star 0
  set BRAMFIFO18_star 0
  set BRAM18 0
  set BRAMFIFO 0
  set BIOB 0
  set DSPs 0
  set TotPower 0
  set design_slack 0
  set design_req 0
  set design_delay 0
  regexp --  {\s*LUT Flip Flop Pairs\s*\|\s*([^[:blank:]]+)} $util_rpt ignore LUTFFPairs
  regexp --  {\s*Slice Registers\s*\|\s*([^[:blank:]]+)} $util_rpt ignore SliceRegisters
  regexp --  {\s*Slice\s*\|\s*([^[:blank:]]+)} $util_rpt ignore Slice
  regexp --  {\s*Slice LUTs\s*\|\s*([^[:blank:]]+)} $util_rpt ignore SliceLUTs
  regexp --  {\s*Slice LUTs\*\s*\|\s*([^[:blank:]]+)} $util_rpt ignore SliceLUTs1
  if { [expr {$LUTFFPairs == 0}] } {
    set LUTFFPairs $SliceLUTs1
    puts $SliceLUTs1
  }
  if { [expr {$SliceLUTs == 0}] } {
    set SliceLUTs $SliceLUTs1
  }
  regexp --  {\s*RAMB36/FIFO36\s*\|\s*([^[:blank:]]+)} $util_rpt ignore BRAMFIFO36
  regexp --  {\s*RAMB18/FIFO18\s*\|\s*([^[:blank:]]+)} $util_rpt ignore BRAMFIFO18
  regexp --  {\s*RAMB36/FIFO\*\s*\|\s*([^[:blank:]]+)} $util_rpt ignore BRAMFIFO36_star
  regexp --  {\s*RAMB18/FIFO\*\s*\|\s*([^[:blank:]]+)} $util_rpt ignore BRAMFIFO18_star
  regexp --  {\s*RAMB18\s*\|\s*([^[:blank:]]+)} $util_rpt ignore BRAM18
  set BRAMFIFO [expr {(2 *$BRAMFIFO36) + $BRAMFIFO18 + (2*$BRAMFIFO36_star) + $BRAMFIFO18_star + $BRAM18}]
  regexp --  {\s*Bonded IOB\s*\|\s*([^[:blank:]]+)} $util_rpt ignore BIOB
  regexp --  {\s*DSPs\s*\|\s*([^[:blank:]]+)} $util_rpt ignore DSPs
  set power_rpt [report_power -return_string]
  regexp --  {\s*Total On-Chip Power \(W\)\s*\|\s*([^[:blank:]]+)} $power_rpt ignore TotPower
  set Timing_Paths [get_timing_paths -max_paths 1 -nworst 1 -setup]
  if { [expr {$Timing_Paths == ""}] } {
    set design_slack 0
    set design_req 0
  } else {
    set design_slack [get_property SLACK $Timing_Paths]
    set design_req [get_property REQUIREMENT  $Timing_Paths]
  }
  if { [expr {$design_slack == ""}] } {
    set design_slack 0
  }
  if { [expr {$design_req == ""}] } {
    set design_req 0
  }
  set design_delay [expr {$design_req - $design_slack}]
  file delete -force encode_report.xml
  set ofile_report [open encode_report.xml w]
  puts $ofile_report "<?xml version=\"1.0\"?>"
  puts $ofile_report "<document>"
  puts $ofile_report "  <application>"
  puts $ofile_report "    <section stringID=\"XILINX_SYNTHESIS_SUMMARY\">"
  puts $ofile_report "      <item stringID=\"XILINX_LUT_FLIP_FLOP_PAIRS_USED\" value=\"$LUTFFPairs\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_SLICE\" value=\"$Slice\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_SLICE_REGISTERS\" value=\"$SliceRegisters\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_SLICE_LUTS\" value=\"$SliceLUTs\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_BLOCK_RAMFIFO\" value=\"$BRAMFIFO\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_IOPIN\" value=\"$BIOB\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_DSPS\" value=\"$DSPs\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_POWER\" value=\"$TotPower\"/>"
  puts $ofile_report "      <item stringID=\"XILINX_DESIGN_DELAY\" value=\"$design_delay\"/>"
  puts $ofile_report "    </section>"
  puts $ofile_report "  </application>"
  puts $ofile_report "</document>"
  close $ofile_report
}; #END PROC
set outputDir .
create_project -in_memory -part xc7z020clg484-1 -force
read_verilog -sv main.sv
synth_design -mode out_of_context -no_iobuf -top main -part xc7z020clg484-1
write_checkpoint -force $outputDir/post_synth.dcp
report_timing_summary -file $outputDir/post_synth_timing_summary.rpt
report_utilization -file $outputDir/post_synth_util.rpt
create_clock -name clk -period 10.000 [get_ports clk]
dump_statistics
opt_design
dump_statistics
report_utilization -file $outputDir/post_opt_design_util.rpt
place_design -directive Explore
report_clock_utilization -file $outputDir/clock_util.rpt
# Optionally run optimization if there are timing violations after placement
if {[get_property SLACK [get_timing_paths -max_paths 1 -nworst 1 -setup]] < 0.5} {
  puts "Found setup timing violations => running physical optimization"
  phys_opt_design
}
write_checkpoint -force $outputDir/post_place.dcp
report_utilization -file $outputDir/post_place_util.rpt
report_timing_summary -file $outputDir/post_place_timing_summary.rpt
dump_statistics
route_design -directive Explore
write_checkpoint -force $outputDir/post_route.dcp
report_route_status -file $outputDir/post_route_status.rpt
report_timing_summary -file $outputDir/post_route_timing_summary.rpt
report_power -file $outputDir/post_route_power.rpt
report_drc -file $outputDir/post_imp_drc.rpt
report_utilization -file $outputDir/post_route_util.rpt
dump_statistics
close_design
close_project
