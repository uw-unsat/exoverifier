#!/bin/sh
opt_no_bash_color=-no-bash-colors
usage="Usage: ./run_tests [$opt_no_bash_color]"
bash_colors=yes

if ([ $# -gt 1 ]) || ([ $# -eq 1 ] && [ $1 != $opt_no_bash_color ]); then 
  echo $usage
  exit 1
fi
if [ $# -eq 1 ] && [ $1 = $opt_no_bash_color ]; then
  bash_colors=no
fi
cd src/test
if [ $bash_colors = yes ]; then
  ./test_runner
else
  ./test_runner -no-bash-colors
fi
