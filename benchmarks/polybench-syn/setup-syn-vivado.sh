#!/bin/bash

#set up
sshhost="$1"
basedir=${2:-"poly-syn-vivado"}

echo "Setting up in $sshhost:$basedir"

echo "Creating directory"
ssh -q "$sshhost" "cd ~; rm -r $basedir; mkdir $basedir"

echo "Copying scripts over"
scp -q syn-vivado.tcl "$sshhost:$basedir"
scp -q syn-vivado.sh "$sshhost:$basedir"
rm syn-list

while read -r benchmark; do
echo "Copying $benchmark over"
name=$(echo "$benchmark" | awk -v FS="/" '{print $NF}')
scp -q "$benchmark.v" "$sshhost:~/$basedir"
echo "$name" >> syn-list
done < benchmark-list-master

echo "Copying syn-list"
scp -q syn-list "$sshhost:$basedir"
