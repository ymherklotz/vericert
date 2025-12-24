timing_rpt=timing_post_pr.rpt
util_rpt=utilization_post_pr.rpt
clk_period=4

workingdir=$(pwd)
synth_summary_rpt=synth_p_r_summary.rpt
str=`grep -A 2 "Timing Report" "${timing_rpt}"`
slack_with_unit=`echo $str | cut -d' ' -f 6`
slack=`echo $slack_with_unit | cut -d'n' -f 1`
actual_cp=`echo "$clk_period - $slack" | bc`
echo "**************************************************" >> $workingdir/$synth_summary_rpt
echo "Timing Summary for the example" >> $workingdir/$synth_summary_rpt
echo "The clk period constraint applied during synthesis is 4ns" >> $workingdir/$synth_summary_rpt
echo "The slack is ${slack}ns" >> $workingdir/$synth_summary_rpt
echo "The actual clk period (CP) is ${actual_cp}ns" >> $workingdir/$synth_summary_rpt

#echo " " >> $workingdir/$synth_summary_rpt
cycle_count_final=$1
echo "The cycles count from simulation is ${cycle_count_final}" >> $workingdir/$synth_summary_rpt
exec_time=`echo "$cycle_count_final * $actual_cp" | bc`
echo "The total execution time is ${exec_time}ns" >> $workingdir/$synth_summary_rpt
echo " " >> $workingdir/$synth_summary_rpt

echo "**************************************************" >> $workingdir/$synth_summary_rpt
echo "Area Summary for the example" >> $workingdir/$synth_summary_rpt

luts_str=`grep "Slice LUTs" "${util_rpt}"`
luts=`echo $luts_str | cut -d'|' -f 3`
echo "The LUTs count is ${luts}" >> $workingdir/$synth_summary_rpt

ffs_str=`grep -m 1 "Slice Registers" "${util_rpt}"`
ffs=`echo $ffs_str | cut -d'|' -f 3`
echo "The FFs count is ${ffs}" >> $workingdir/$synth_summary_rpt

dsps_str=`grep -m 1 "DSPs" "${util_rpt}"`
dsps=`echo $dsps_str | cut -d'|' -f 3`
echo "The DSPs count is ${dsps}" >> $workingdir/$synth_summary_rpt
