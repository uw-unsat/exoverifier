#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_ADD tests"
               (test-case+ "test ALU ADD X" (test-insn '(BPF_ALU BPF_ADD BPF_X)))
               (test-case+ "test ALU64 ADD X" (test-insn '(BPF_ALU64 BPF_ADD BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
