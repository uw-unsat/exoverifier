#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_MOV tests"
               (test-case+ "test ALU MOV X" (test-insn '(BPF_ALU BPF_MOV BPF_X)))
               (test-case+ "test ALU64 MOV X" (test-insn '(BPF_ALU64 BPF_MOV BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
