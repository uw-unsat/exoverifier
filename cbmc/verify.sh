#!/usr/bin/env bash
set -euo pipefail;
cbmc --z3 tnum.c;
