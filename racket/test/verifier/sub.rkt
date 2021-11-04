#lang rosette

(require "common.rkt"
         serval/lib/unittest
         serval/lib/solver
         rosette/lib/roseunit)

(define verifier-tests
  (test-suite+ "BPF_SUB tests"
               (test-case+ "test ALU SUB X" (test-insn '(BPF_ALU BPF_SUB BPF_X)))
               (test-case+ "test ALU64 SUB X" (test-insn '(BPF_ALU64 BPF_SUB BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
