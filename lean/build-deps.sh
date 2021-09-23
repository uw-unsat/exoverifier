#!/usr/bin/env bash
set -euo pipefail;
cd pkgs/aiger && ./configure.sh && make -j$(nproc) && cd ../..;
cd pkgs/druplig && ./configure.sh && make -j$(nproc) && cd ../..;
cd pkgs/lingeling && ./configure.sh && make -j$(nproc) && cd ../..;
cd pkgs/picosat && ./configure.sh && make -j$(nproc) && cd ../..;
cd pkgs/drat-trim && make -j$(nproc) && cd ../..;
cd pkgs/c32sat && ./configure && make -j$(nproc) && cd ../..;

