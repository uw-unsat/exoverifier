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

  (define env (fresh-bpf-verifier-env))

  (define bpf-cpu (bpf:init-cpu))
  (bpf:set-cpu-regs! bpf-cpu (struct-copy bpf:regs bpf-regs))

  ; Assume abstract state initially approximates cpu
  (assume (bpf-verifier-env-contains? env bpf-cpu))

  ; Step the instruction on concrete interrpreter and through the verifier
  (define insn (bpf:insn op 'r0 'r1 #f #f))
  (bpf:interpret-insn bpf-cpu insn #:next #f)
  (adjust_reg_min_max_vals env insn)

  ; Assert that the resulting state is a correct approximation.
  (assert (bpf-verifier-env-contains? env bpf-cpu)))

(define verifier-tests
  (test-suite+ "Verifier tests"
               (test-case+ "test ALU ADD X" (test-insn '(BPF_ALU BPF_ADD BPF_X)))
               (test-case+ "test ALU64 ADD X" (test-insn '(BPF_ALU64 BPF_ADD BPF_X)))
               (test-case+ "test ALU SUB X" (test-insn '(BPF_ALU BPF_SUB BPF_X)))
               (test-case+ "test ALU64 SUB X" (test-insn '(BPF_ALU64 BPF_SUB BPF_X)))
               (test-case+ "test ALU AND X" (test-insn '(BPF_ALU BPF_AND BPF_X)))
               (test-case+ "test ALU64 AND X" (test-insn '(BPF_ALU64 BPF_AND BPF_X)))
               (test-case+ "test ALU OR X" (test-insn '(BPF_ALU BPF_OR BPF_X)))
               (test-case+ "test ALU64 OR X" (test-insn '(BPF_ALU64 BPF_OR BPF_X)))
               (test-case+ "test ALU XOR X" (test-insn '(BPF_ALU BPF_XOR BPF_X)))
               (test-case+ "test ALU64 XOR X" (test-insn '(BPF_ALU64 BPF_XOR BPF_X)))))

(module+ test
  (time (with-prefer-boolector (run-tests verifier-tests))))
