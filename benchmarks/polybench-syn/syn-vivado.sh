#! /bin/bash

#setup
while read -r benchmark; do
  echo "Setting up $benchmark"
  rm -r "$benchmark-vivado"
  mkdir "$benchmark-vivado"
  cp "$benchmark.v" "$benchmark-vivado/top.v"
done < syn-list

#synthesis
count=0
while read -r benchmark; do
  echo "Synthesising $benchmark"

  cd "$benchmark-vivado" || {
    echo "$benchmark dir does not exist"
    continue
  }
  vivado -mode batch -source ../syn-vivado.tcl
  cd ..
  (( count=count+1 ))

  if [ "$count" -eq 4 ]; then
  echo "I am here"
  wait
  count=0
  fi
done < syn-list

if [ $count -lt 4 ]; then
wait
fi

#extract
while read -r benchmark ; do
  cd "$benchmark-vivado" || {
    echo "$benchmark-vivado does not exist"
    continue
  }

  pwd
  logfile="vivado.log"
  timingfile="worst_timing.txt"

  luts=$(grep "|LUT" "$logfile" | cut -d'|' -f 4 | paste -sd + | bc)
  brams=$(sed -n -e "s/BRAMs: \([0-9]\+\).*$/\1/p" "$logfile")
  dsps=$(sed -n -e "s/DSPs: \([0-9]\+\).*$/\1/p" "$logfile")
  cells=$(grep -A4 "Report Instance Areas:" "$logfile" | tail -1 | cut -d '|' -f5 | tr -d [:space:])
  slack=$(sed -n -e 's/\s\+slack\s\+\(-\?[0-9.]\+\)/\1ns/p' "$timingfile" | tr -d [:space:])

  echo "$benchmark,$slack,$luts,$brams,$dsps" >> results
done < syn-list

