#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_RSH tests"
               (test-case+ "test ALU RSH X" (test-insn '(BPF_ALU BPF_RSH BPF_X)))
               (test-case+ "test ALU64 RSH X" (test-insn '(BPF_ALU64 BPF_RSH BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
