#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_LSH tests"
               (test-case+ "test ALU LSH X" (test-insn '(BPF_ALU BPF_LSH BPF_X)))
               (test-case+ "test ALU64 LSH X" (test-insn '(BPF_ALU64 BPF_LSH BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
