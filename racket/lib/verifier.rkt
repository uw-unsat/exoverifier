#lang rosette

(require "tnum.rkt"
         (prefix-in bpf: serval/bpf))

(provide (all-defined-out))

(struct state (tnums) #:mutable #:transparent)

; Make a fresh state
(define (make-state)
  (define tnums
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (fresh-tnum 64)))
  (state (apply bpf:regs tnums)))

(define (adjust_scalar_min_max_vals abs insn rd rs)
  (define op (bpf:insn-code insn))
  (define tnums (state-tnums abs))

  (case (bpf:insn-code insn)
    [((BPF_ALU64 BPF_ADD BPF_X))
     (define dst (bpf:@reg-ref tnums rd))
     (define src (bpf:@reg-ref tnums rs))
     (bpf:@reg-set! tnums rd (tnum-add dst src))]
    [else (assert #f)]))

(define (adjust_reg_min_max_vals abs insn)
  (define rd (bpf:insn-dst insn))
  (define rs (bpf:insn-src insn))
  (adjust_scalar_min_max_vals abs insn rd rs))

; Whether concrete state "cpu" is approximated by "abs".
(define (state-contains? abs cpu)
  (define tnums (state-tnums abs))
  (define l
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (define r (bpf:idx->reg i))
      (tnum-contains? (bpf:@reg-ref tnums r) (bpf:reg-ref cpu r))))
  (apply && l))
