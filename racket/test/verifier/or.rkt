#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_OR tests"
               (test-case+ "test ALU OR X" (test-insn '(BPF_ALU BPF_OR BPF_X)))
               (test-case+ "test ALU64 OR X" (test-insn '(BPF_ALU64 BPF_OR BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
