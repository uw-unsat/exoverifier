#!/bin/sh
echo "((a0 > 0) && (a0 <= 127) && (b0 >= 0) && (b0 <= 127)"
i=1
while [ $i -le 10 ]
do
  im1=`expr $i - 1`
  echo "&& ((b$im1 != 0) ? (b$i == a$im1 % b$im1) && (a$i == b$im1)"
  echo ": (a$i == a$im1) && (b$i == b$im1))"  
  i=`expr $i + 1`
done
echo ") => (((d > 0) && (d <= 127) && (a0 % d == 0) && (b0 % d == 0)) => (a10 % d == 0))"
