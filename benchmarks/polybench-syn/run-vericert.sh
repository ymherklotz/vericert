#! /bin/bash 

top=$(pwd)
 #set up
while read benchmark ; do
   echo "Running "$benchmark
   clang -Wall -Werror -fsanitize=undefined $benchmark.c -o $benchmark.o
   ./$benchmark.o
   cresult=$(echo $?)
   echo "C output: "$cresult
   ../../bin/vericert -DSYNTHESIS -O0 -finline --debug-hls $benchmark.c -o $benchmark.v
   iverilog -o $benchmark.iver -- $benchmark.v
   ./$benchmark.iver > $benchmark.tmp
   veriresult=$(tail -1 $benchmark.tmp | cut -d' ' -f2)
   cycles=$(tail -4 $benchmark.tmp | head -1 | tr -s ' ' | cut -d' ' -f3)
   echo "Veri output: "$veriresult
  
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
