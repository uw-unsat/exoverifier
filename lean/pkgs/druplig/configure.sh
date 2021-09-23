#!/bin/sh
sig=no
debug=no
while [ $# -gt 0 ]
do
  case $1 in
    -h) echo "usage: configure.sh [-h][-g][--sig|--no-sig]"; exit 0;;
    -g) debug=yes;;
    --sig) sig=yes;;
    --no-sig) sig=no;;
    *) echo "*** invalid command line option '$1' (try '-h')"; exit 1;;
  esac
  shift
done
CC=gcc
CFLAGS="-Wall"
if [ $debug = yes ]
then
  CFLAGS="$CFLAGS -g3"
else
  CFLAGS="$CFLAGS -O3 -DNDEBUG"
fi
[ $sig = no ] && CFLAGS="$CFLAGS -DNSIG"
CFLAGS="$CFLAGS -DVERSION=\\\\\"`cat VERSION`\\\\\""
echo "$CC $CFLAGS"
rm -f makefile
sed -e "s,@CC@,$CC," -e "s,@CFLAGS@,$CFLAGS," makefile.in > makefile
