#! /bin/bash

#setup
while read benchmark ;
do
echo "Setting up "$benchmark
rm -r $benchmark
mkdir $benchmark
cp $benchmark.v $benchmark/top.v

done < syn-list

#synthesis

count=0
while read benchmark ;

do
echo "Synthesising "$benchmark
cd $benchmark
quartus_sh -t ../quartus_synth.tcl &
let "count=count+1"
cd ..

if [ $count -eq 4 ]
then
echo "I am here"
wait
count=0
fi

done < syn-list

if [ $count -lt 4 ]
then
wait
fi

#extract
while read benchmark ; do
  cd $benchmark
  echo $(pwd)
  freq=$(grep MHz syn.sta.rpt | tail -2 | head -1 | awk '{print $2}')
  lut=$(sed -n -e 8p syn.fit.summary | awk '{print $6}' | sed 's/,//g')
  regs=$(sed -n -e 9p syn.fit.summary | awk '{print $4}')
  bram=$(sed -n -e 13p syn.fit.summary | awk '{print $5}')
  dsp=$(sed -n -e 14p syn.fit.summary | awk '{print $5}')
  cd ..
  echo $benchmark","$freq","$lut","$regs","$bram","$dsp >> results
done < syn-list

