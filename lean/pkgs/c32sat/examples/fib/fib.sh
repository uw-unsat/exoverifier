#!/bin/sh

if [ $# -ne 1 ]; then
  echo "Usage: fib.sh <n>"
  exit
fi

if [ $1 -lt 3 ]; then
  echo "n has to be > 2"
  exit
fi
echo "f1 == 1 && f2 == 1"
i=3
while [ $i -le $1 ]
do
  echo "&& f$i == f`expr $i - 1` + f`expr $i - 2`"
  i=`expr $i + 1`
done
