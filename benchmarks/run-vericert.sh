#! /bin/bash

# Kill children on Ctrl-c. I have no idea how or why this works
trap 'trap " " SIGTERM; kill 0; wait;' SIGINT SIGTERM

function error() { echo "$1" >&2; }
function crash() { echo "$1" >&2; exit 1; }
function info() { echo "$1" >&2; }

[ $# -ge 1 ] || crash "Usage: $0 <benchmark-suite>"
benchmark_dir="$1"

[ -f "$benchmark_dir/benchmark-list-master" ] || crash "$benchmark_dir/benchmark-list-master does not exist"

vericert=../bin/vericert
[ -x $vericert ] || crash "Vericert executable does not exist or is not marked as executable. Did you run make; make install?"

function run_benchmark() {
   benchmark_rel="$1"
   benchmark="$benchmark_dir/$benchmark_rel"
   [ -f "$benchmark.c" ] || { error "$benchmark.c does not exist"; return; }

   info "[$benchmark] Running"
   clang -Wall -Werror -fsanitize=undefined "$benchmark".c -o "$benchmark".o
   ./"$benchmark".o > "$benchmark".clog
   cresult=$(cut -d' ' -f2 "$benchmark.clog")
   info "[$benchmark] C output: $cresult"
   { time ../bin/vericert -DSYNTHESIS --debug-hls "$benchmark.c" -o "$benchmark.v" ; vericert_result=$? ; } 2> "$benchmark".comp

   iverilog -o "$benchmark".iver -- "$benchmark".v
   iverilog_result=$?

   timeout 10m ./"$benchmark".iver > "$benchmark".tmp
   if [ $? -eq 124 ]; then
      timeout=1
   else
      veriresult="$(tail -1 "$benchmark".tmp | cut -d' ' -f2)"
   fi
   cycles="$(tail -4 "$benchmark".tmp | head -1 | tr -s ' ' | cut -d' ' -f3)"
   ctime="$(head -2 "$benchmark".comp | tail -1 | xargs | cut -d' ' -f2 | cut -d'm' -f2 | sed 's/s//g')"
   info "[$benchmark] Veri output: $veriresult"


   if [ -n "$timeout" ]; then
      info "[$benchmark] FAIL: Verilog timed out"
      result="timeout"
   elif [ "$vericert_result" -ne 0 ]; then
      #Undefined
      info "[$benchmark] FAIL: Vericert failed"
      result="compile error"
   elif [ "$iverilog_result" -ne 0 ]; then
      #Undefined
      info "[$benchmark] FAIL: iverilog failed"
      result="elaboration error"
   elif [ -z "$veriresult" ]; then
      #Undefined
      info "[$benchmark] FAIL: Verilog returned nothing"
      result="timeout"
   elif [ "$veriresult" == "x" ]; then
      # Don't care
      info "[$benchmark] FAIL: Verilog returned don't cares"
      result="dontcare"
   elif [ "$cresult" -ne "$veriresult" ]; then
      # unequal result
      info "[$benchmark] FAIL: Verilog and C output do not match!"
      result="incorrect result"
   else
      info "[$benchmark] PASS"
      result="pass"
   fi
   name=$(echo "$benchmark" | awk -v FS="/" '{print $NF}')
   echo "$name,$cycles,$ctime,$result"
}

while read -r benchmark_rel; do
 run_benchmark "$benchmark_rel" >> "$benchmark_dir-exec.csv" &
done < "$benchmark_dir/benchmark-list-master"
wait
