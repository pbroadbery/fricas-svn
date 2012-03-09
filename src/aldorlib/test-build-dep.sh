#!/bin/bash

# Quick test for build script.
contains() {
    if [ ! -f $2 ] ; then return 1; fi
    for i in $(cat $2); do if [ $i = $1 ]; then return 0; fi; done
    return 1
}

precedes() {
    if [ ! -f $3 ] ; then return 1; fi
    found=0
    for i in $(cat $3); do
	if [ $i = $1 ]; then found=1; fi; 
	if [ $found = 1 -a $i = $2 ]; then return 0; fi; 
    done
    return 1
}

oneOf() {
    if [ ! -f $2 ] ; then return 1; fi
    found=0
    for i in $(cat $2); do
	if [ $found = 1 -a $i = $1 ]; then return 1; fi; 
	if [ $i = $1 ]; then found=1; fi; 
    done
    return 0
}

if [ ! -x ./build-dep ];
then
    echo "No script"
    exit 1
fi

if ! readlink -f $0 > /dev/null;
then
    echo "No readlink. No testing"
fi

thisdir=$(readlink -f $(dirname $0))
build_dep=$thisdir/build-dep

if [ ! -x $build_dep ];
then
    echo "still no script"
    exit 1
fi

testdir=/var/tmp/$$

mkdir -p $testdir

cd $testdir
set -x
set -e

echo > lang.req

$build_dep lang.dep lang.req
if [ ! -f lang.dep ];
then 
    echo "no file created"
    exit 1
fi

for i in $(cat lang.dep); 
do
    echo "lang.dep should be empty -[$i]"
    exit 1
done
# Basic.req = "lang"
# Next.req = "Basic"
# Next2.req = "Basic"
# Top.req = Next Next2 Basic
echo > Basic.req
echo lang >> Basic.req

$build_dep Basic.dep Basic.req
contains lang Basic.dep 

echo > Next.req
echo Basic >> Next.req

$build_dep Next.dep Next.req
precedes lang Basic Next.dep

echo > Next2.req
echo Basic >> Next2.req

$build_dep Next2.dep Next2.req
precedes lang Basic Next2.dep

echo > Top.req
echo Next >> Top.req
echo Next2 >> Top.req
echo Basic >> Top.req

$build_dep Top.dep Top.req
echo ===
cat Top.dep
echo ===

precedes lang Basic Top.dep
precedes Basic Next Top.dep
precedes Basic Next2 Top.dep
oneOf Basic Top.dep

echo missing > fail.req
if $build_dep fail.dep fail.req
then
    echo should have failed
    exit 1
fi

rm -rf $testdir

