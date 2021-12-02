#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_ARSH tests"
               (test-case+ "test ALU ARSH X" (test-insn '(BPF_ALU BPF_ARSH BPF_X)))
               (test-case+ "test ALU64 ARSH X" (test-insn '(BPF_ALU64 BPF_ARSH BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
