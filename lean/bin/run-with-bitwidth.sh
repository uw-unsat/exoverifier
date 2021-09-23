#!/bin/bash
set -euo pipefail;

if [ $# -ne 2 ]; then
	echo "Usage: ./bin/run-with-bitwidth.sh [number] [path/to/file.lean]" > /dev/stderr
	exit 1
fi

rm -f "${2%.lean}.olean";
env BITWIDTH="$1" lean --tstack=4000000 --mem=4000 --make "$2";
