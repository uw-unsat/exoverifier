#!/bin/sh

if [ $# -ne 1 ]; then
  echo "Usage: gcdmax8bits.sh <max_loops>"
  exit
fi
echo "(a0 > 0) && (a0 <= 127) && (b0 >= 0) && (b0 <= 127) && (b`expr $1 - 1` != 0)"
i=1
while [ $i -le $1 ]
do
  im1=`expr $i - 1`
  echo "&& ((b$im1 != 0) ? (b$i == a$im1 % b$im1) && (a$i == b$im1)"
  echo ": (a$i == a$im1) && (b$i == b$im1))"   
  i=`expr $i + 1`
done
