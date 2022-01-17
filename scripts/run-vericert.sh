#!/usr/bin/env bash

rm exec.csv

top=$(pwd)
 #set up
while read benchmark ; do
   echo "Running "$benchmark
   ./$benchmark.gcc > $benchmark.clog
   cresult=$(cat $benchmark.clog | cut -d' ' -f2)
   echo "C output: "$cresult
   ./$benchmark.iver > $benchmark.tmp
   veriresult=$(tail -1 $benchmark.tmp | cut -d' ' -f2)
   cycles=$(tail -2 $benchmark.tmp | head -1 | tr -s ' ' | cut -d' ' -f2)
   echo "Verilog output: "$veriresult
  
   #Undefined checks
   if test -z $veriresult 
   then
   echo "FAIL: Verilog returned nothing"
   #exit 0
   fi
   
   # Don't care checks
   if [ $veriresult == "x" ] 
   then
   echo "FAIL: Verilog returned don't cares"
   #exit 0
   fi
  
  # unequal result check
   if [ $cresult -ne $veriresult ] 
   then 
   echo "FAIL: Verilog and C output do not match!"
   #exit 0 
   else 
   echo "PASS"
   fi
   name=$(echo $benchmark | awk -v FS="/" '{print $NF}')
   echo $name","$cycles >> exec.csv
done < benchmark-list-master
