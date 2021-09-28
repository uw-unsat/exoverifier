#!/usr/bin/env bash
set -euo pipefail;

NANODA="${HOME}/repo/nanoda_lib/target/release/examples/basic"
TREPPLEIN="${HOME}/trepplein.sh"

# Proof generation performance
hyperfine -r 2 -L size 20,40,80,160 -- './scripts/make_proof.py --verifier absint test/bpf/examples/common/large-{size}.bin test/bpf/examples/common/large-{size}-absint.lef';
hyperfine -r 2 -L size 20,40,80,160 -- "${NANODA} 8 test/bpf/examples/common/large-{size}-absint.lef";
hyperfine -r 2 -L size 20,40,80,160 -- "${TREPPLEIN} test/bpf/examples/common/large-{size}-absint.lef -p test_bpf.program_safety";
hyperfine -r 2 -L size 20,40,80,160 -- "leanchecker test/bpf/examples/common/large-{size}-absint.lef test_bpf.program_safety";