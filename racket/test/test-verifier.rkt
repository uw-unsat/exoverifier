#lang rosette

(require "../lib/verifier.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/solver
         serval/lib/unittest
         (prefix-in bpf: serval/bpf))

(define (test-insn op)

  ; Create symbolic register content for each BPF register
  (define-symbolic* r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ax (bitvector 64))
  (define bpf-regs (bpf:regs r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 ax))

  (define abs (make-state))

  (define bpf-cpu (bpf:init-cpu))
  (bpf:set-cpu-regs! bpf-cpu (struct-copy bpf:regs bpf-regs))

  ; Assume abstract state initially approximates cpu
  (assume (state-contains? abs bpf-cpu))

  ; Step the instruction on concrete interrpreter and through the verifier
  (define insn (bpf:insn op 'r0 'r1 #f #f))
  (bpf:interpret-insn bpf-cpu insn #:next #f)
  (adjust_reg_min_max_vals abs insn)

  ; Assert that the resulting state is a correct approximation.
  (assert (state-contains? abs bpf-cpu)))

(define verifier-tests
  (test-suite+ "Verifier tests"
               (test-case+ "test ALU64 ADD X" (test-insn '(BPF_ALU64 BPF_ADD BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
