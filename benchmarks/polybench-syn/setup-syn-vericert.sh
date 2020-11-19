#! /bin/bash 

top=$(pwd)
 #set up
 basedir=poly-syn
 sshhost=$1
 ssh $sshhost "cd ~; rm -r $basedir"
 ssh $sshhost "cd ~; mkdir $basedir"
 scp quartus_synth.tcl $sshhost:$basedir 
 scp syn-remote.sh $sshhost:$basedir 
 rm syn-list 

 while read benchmark ; 
 do
 echo "Copying "$benchmark" over"
 name=$(echo $benchmark | awk -v FS="/" '{print $NF}')
 echo "Name: "$name
 benchdir="~/$basedir/$name"
 scp $benchmark.v $sshhost:~/$basedir
 echo $name >> syn-list
 done < benchmark-list-master

 # copy list over
 scp syn-list $sshhost:$basedir
