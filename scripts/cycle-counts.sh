#!/bin/bash

echo "##################################################"
echo "# Compiling benchmark: vericert-hyperblock"
echo "##################################################"
VERICERT=vericert VERICERT_OPTS="-DSYNTHESIS -fschedule -fif-conv" make

echo "##################################################"
echo "# Running benchmark: vericert-hyperblock"
echo "##################################################"
run-vericert.sh
mv exec.csv vericert-hyperblock-cycles.csv
make clean

echo "##################################################"
echo "# Compiling benchmark: vericert-list-scheduling"
echo "##################################################"
VERICERT=vericert VERICERT_OPTS="-DSYNTHESIS -fschedule" make

echo "##################################################"
echo "# Running benchmark: vericert-list-scheduling"
echo "##################################################"
run-vericert.sh
mv exec.csv vericert-list-scheduling-cycles.csv
make clean

echo "##################################################"
echo "# Compiling benchmark: vericert-original"
echo "##################################################"
VERICERT=vericert-original VERICERT_OPTS="-DSYNTHESIS" make

echo "##################################################"
echo "# Compiling benchmark: vericert-original"
echo "##################################################"
run-vericert.sh
mv exec.csv vericert-original-cycles.csv
make clean
