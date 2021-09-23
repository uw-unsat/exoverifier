#!/bin/bash

function square {
  x1=0
  y1=0
  x2=0
  y2=0
  in1=$1
  in2=$2
  line=""
  for ((i=1;i<=9;i+=1))
  do
    if [ $y1 -eq 2 ]; then
      ((y2=0))
      ((x2=x1+1))
    else 
      ((x2=x1))
      ((y2=y1+1))
    fi 
    for ((j=$i+1;j<=9;j+=1))
    do
      line="$line && m$((in1+x1))$((in2+y1)) != m$((in1+x2))$((in2+y2))"
      if [ $y2 -eq 2 ]; then
        ((y2=0))
        ((x2++))
      else 
        ((y2++))
      fi
    done
    echo $line
    line=""
    if [ $y1 -eq 2 ]; then
      ((y1=0))
      ((x1++))
    else 
      ((y1++))
    fi
  done
}

line=""

for ((i=1;i<=9;i+=1))
do
  for ((j=1;j<=9;j+=1))
  do
    echo "&& m$i$j > 0 && m$i$j < 10"
  done
done
for ((i=1;i<=9;i+=1))
do
  for ((j=1;j<=9;j+=1))
  do
    for ((k=j+1;k<=9;k+=1))
    do
      line="$line && m$i$j != m$i$k"
    done
  done
  echo $line
  line=""
done
for ((i=1;i<=9;i+=1))
do
  for ((j=1;j<=9;j+=1))
  do
    for ((k=j+1;k<=9;k+=1))
    do
      line="$line && m$j$i != m$k$i"
    done
  done
  echo $line
  line=""
done
square 1 1
square 1 4
square 1 7
square 4 1
square 4 4
square 4 7
square 7 1
square 7 4
square 7 7
  
