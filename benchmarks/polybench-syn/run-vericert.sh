#! /bin/bash 

top=$(pwd)
 #set up
while read benchmark ; do
   echo "Running "$benchmark
   clang -Wall -Werror -fsanitize=undefined $benchmark.c -o $benchmark.o
   ./$benchmark.o > $benchmark.clog
   cresult=$(cat $benchmark.clog | cut -d' ' -f2)
   echo "C output: "$cresult
   { time ../../bin/vericert -DSYNTHESIS -finline --debug-hls $benchmark.c -o $benchmark.v ; } 2> $benchmark.comp
   iverilog -o $benchmark.iver -- $benchmark.v
   ./$benchmark.iver > $benchmark.tmp
   veriresult=$(tail -1 $benchmark.tmp | cut -d' ' -f2)
   cycles=$(tail -4 $benchmark.tmp | head -1 | tr -s ' ' | cut -d' ' -f3)
   ctime=$(cat $benchmark.comp | head -2 | tail -1 | xargs | cut -d' ' -f2 | cut -d'm' -f2 | sed 's/s//g')
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
   echo $name","$cycles","$ctime >> exec.csv 
done < benchmark-list-master
