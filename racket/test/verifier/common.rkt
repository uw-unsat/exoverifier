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

  (define dst 'r0)
  (define src 'r1)

  (define dst-val-pre (bpf:reg-ref bpf-cpu dst))
  (define src-val-pre (bpf:reg-ref bpf-cpu src))
  (define dst-state-pre (struct-copy bpf-reg-state (bpf:@reg-ref (bpf-verifier-env-regs env) dst)))
  (define src-state-pre (struct-copy bpf-reg-state (bpf:@reg-ref (bpf-verifier-env-regs env) src)))

  ; Step the instruction on concrete interrpreter and through the verifier
  (define insn (bpf:insn op dst src #f #f))
  (bpf:interpret-insn bpf-cpu insn #:next #f)
  (adjust_reg_min_max_vals env insn)

  (define dst-val-post (bpf:reg-ref bpf-cpu dst))
  (define dst-state-post (struct-copy bpf-reg-state (bpf:@reg-ref (bpf-verifier-env-regs env) dst)))

  ; Assert that the resulting state is a correct approximation.
  (bug-assert
   (bpf-verifier-env-contains? env bpf-cpu)
   #:msg
   (lambda (m)
     (set!
      m
      (complete-solution
       m
       (symbolics
        (list src-val-pre dst-val-post dst-val-pre src-state-pre dst-state-pre dst-state-post))))
     (format
      "\n{\"dst_state_pre\": ~a, \"dst_val_pre\": \"~a\", \"src_state_pre\": ~a, \"src_val_pre\": \"~a\", \"dst_state_post\": ~a, \"dst_val_post\": \"~a\"}"
      (bpf-reg-state->json (evaluate dst-state-pre m))
      (evaluate dst-val-pre m)
      (bpf-reg-state->json (evaluate src-state-pre m))
      (evaluate src-val-pre m)
      (bpf-reg-state->json (evaluate dst-state-post m))
      (evaluate dst-val-post m))))

  ; Asser that invariants still hold
  (bug-assert (bpf-verifier-env-invariants env)))

(define verifier-tests
  (test-suite+ "Verifier tests"
               (test-case+ "Test assumptions satisfiable" (test-assumptions-satisfiable))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
