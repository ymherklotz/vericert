#! /bin/bash 

#set up
while read -r benchmark ; do
   echo "Running $benchmark"
   clang -Wall -Werror -fsanitize=undefined "$benchmark".c -o "$benchmark".o
   ./"$benchmark".o > "$benchmark".clog
   cresult="$(cut -d' ' -f2 "$benchmark".clog)"
   echo "C output: $cresult"
   { time ../../bin/vericert -DSYNTHESIS $@ --debug-hls "$benchmark".c -o "$benchmark".v ; vericert_result=$? ; } 2> "$benchmark".comp
   iverilog -o "$benchmark".iver -- "$benchmark".v
   iverilog_result=$?

   timeout 1m ./"$benchmark".iver > "$benchmark".tmp
   if [ $? -eq 124 ]; then
      timeout=1
   else
      veriresult="$(tail -1 "$benchmark".tmp | cut -d' ' -f2)"
   fi
   cycles="$(tail -4 "$benchmark".tmp | head -1 | tr -s ' ' | cut -d' ' -f3)"
   ctime="$(head -2 "$benchmark".comp | tail -1 | xargs | cut -d' ' -f2 | cut -d'm' -f2 | sed 's/s//g')"
   echo "Veri output: $veriresult"

   if [ -n "$timeout" ]; then
      echo "FAIL: Verilog timed out"
      result="timeout"
   elif [ "$vericert_result" -ne 0 ]; then
      #Undefined
      echo "FAIL: Vericert failed"
      result="compile error"
   elif [ "$iverilog_result" -ne 0 ]; then
      #Undefined
      echo "FAIL: iverilog failed"
      result="elaboration error"
   elif [ -z "$veriresult" ]; then
      #Undefined
      echo "FAIL: Verilog returned nothing"
      result="timeout"
   elif [ "$veriresult" == "x" ]; then
      # Don't care
      echo "FAIL: Verilog returned don't cares"
      result="dontcare"
   elif [ "$cresult" -ne "$veriresult" ]; then
      # unequal result
      echo "FAIL: Verilog and C output do not match!"
      result="incorrect result"
   else
      echo "PASS"
      result="pass"
   fi
   name=$(echo "$benchmark" | awk -v FS="/" '{print $NF}')
   echo "$name,$cycles,$ctime,$result,$cresult,$veriresult" >> exec.csv
done < benchmark-list-master
