#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_AND tests"
               (test-case+ "test ALU AND X" (test-insn '(BPF_ALU BPF_AND BPF_X)))
               (test-case+ "test ALU64 AND X" (test-insn '(BPF_ALU64 BPF_AND BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
