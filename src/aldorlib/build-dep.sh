#!/bin/bash

target=$1 
reqfile=$2

#for i in $(cat $reqfile); do
#   echo $i $(cat $i.dep); 
#done | tsort > $target

#exit 0
missing() {
    for i in $2;
    do
	if [ $1 = $i ];
	then return 1; fi
    done
    return 0
}

names=
for i in $(cat $reqfile)
do
    if ! $(missing $i $names);
    then
	continue
    fi
    if [ ! -f $i.dep ];
    then 
	echo "Missing $i.dep"
	exit 1
    fi
    for j in $(cat $i.dep);
    do
	if $(missing $j "$names");
	then
	    names="$names $j"
	fi
    done
    names="$names $i"
done

rm -f $target
touch $target
for i in $names;
do
    echo $i >> $target
done

