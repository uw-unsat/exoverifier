#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_XOR tests"
               (test-case+ "test ALU XOR X" (test-insn '(BPF_ALU BPF_XOR BPF_X)))
               (test-case+ "test ALU64 XOR X" (test-insn '(BPF_ALU64 BPF_XOR BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
