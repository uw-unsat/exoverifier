#lang rosette

(require "../../lib/verifier.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/solver
         serval/lib/unittest
         (prefix-in bpf: serval/bpf))

(provide (all-defined-out))

; Check that the assumptions are satisfiable
(define (test-assumptions-satisfiable)
  (define-symbolic* r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ax (bitvector 64))
  (define bpf-regs (bpf:regs r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ax))
  (define bpf-cpu (bpf:init-cpu))
  (bpf:set-cpu-regs! bpf-cpu (struct-copy bpf:regs bpf-regs))

  (define env (fresh-bpf-verifier-env))

  (check-sat? (solve (assert (&& (bpf-verifier-env-invariants env)
                                 (bpf-verifier-env-contains? env bpf-cpu))))))

(define (test-insn op)
  ; Create symbolic register content for each BPF register
  (define-symbolic* r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ax (bitvector 64))
  (define bpf-regs (bpf:regs r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ax))

  (define env (fresh-bpf-verifier-env))

  (define bpf-cpu (bpf:init-cpu))
  (bpf:set-cpu-regs! bpf-cpu (struct-copy bpf:regs bpf-regs))

  ; Assume environment invariants hold
  (assume (bpf-verifier-env-invariants env))

  ; Assume abstract state initially approximates cpu
  (assume (bpf-verifier-env-contains? env bpf-cpu))

  ; Step the instruction on concrete interrpreter and through the verifier
  (define insn (bpf:insn op 'r0 'r1 #f #f))
  (bpf:interpret-insn bpf-cpu insn #:next #f)
  (adjust_reg_min_max_vals env insn)

  ; Assert that the resulting state is a correct approximation.
  (assert (bpf-verifier-env-contains? env bpf-cpu))

  ; Asser that invariants still hold
  (assert (bpf-verifier-env-invariants env)))

(define verifier-tests
  (test-suite+ "Verifier tests"
               (test-case+ "Test assumptions satisfiable" (test-assumptions-satisfiable))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
