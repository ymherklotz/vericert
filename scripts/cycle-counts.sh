#!/bin/bash

target=""
if [[ ! -z $1 ]]; then
    mv benchmark-list-master benchmark-list-master.bck
    echo "$1" >benchmark-list-master
    target="$1"
else
    git checkout benchmark-list-master
fi

echo "##################################################"
echo "# Compiling and running benchmark: bambu-opt"
echo "##################################################"
cat benchmark-list-master | xargs -P8 -n1 run-bambu.sh opt
mv exec.csv bambu-opt-cycles.csv
git clean -dfx -e '*.csv'

echo "##################################################"
echo "# Compiling and running benchmark: bambu-opt"
echo "##################################################"
cat benchmark-list-master | xargs -P8 -n1 run-bambu.sh noopt
mv exec.csv bambu-noopt-cycles.csv
git clean -dfx -e '*.csv'

echo "##################################################"
echo "# Compiling benchmark: vericert-hyperblock"
echo "##################################################"
VERICERT=vericert VERICERT_OPTS="-DSYNTHESIS -fschedule -fif-conv" make -j $target

echo "##################################################"
echo "# Running benchmark: vericert-hyperblock"
echo "##################################################"
run-vericert.sh
mv exec.csv vericert-hyperblock-cycles.csv
git clean -dfx -e '*.csv'

echo "##################################################"
echo "# Compiling benchmark: vericert-list-scheduling"
echo "##################################################"
VERICERT=vericert VERICERT_OPTS="-DSYNTHESIS -fschedule" make -j $target

echo "##################################################"
echo "# Running benchmark: vericert-list-scheduling"
echo "##################################################"
run-vericert.sh
mv exec.csv vericert-list-scheduling-cycles.csv
git clean -dfx -e '*.csv'

echo "##################################################"
echo "# Compiling benchmark: vericert-original"
echo "##################################################"
VERICERT=vericert-original VERICERT_OPTS="-DSYNTHESIS" make -j $target

echo "##################################################"
echo "# Compiling benchmark: vericert-original"
echo "##################################################"
run-vericert.sh
mv exec.csv vericert-original-cycles.csv

if [[ ! -z $1 ]]; then
    mv benchmark-list-master.bck benchmark-list-master
fi

git clean -dfx -e '*.csv'
