#lang rosette

(require "tnum.rkt"
         (prefix-in bpf: serval/bpf))

(provide (all-defined-out))

(struct bpf-reg-state (var-off) #:mutable #:transparent)

(struct bpf-verifier-env (regs) #:mutable #:transparent)

; Make a fresh register state
(define (fresh-bpf-reg-state) (bpf-reg-state (fresh-tnum 64)))

; Make a fresh verifier environment (register mapping)
(define (fresh-bpf-verifier-env)
  (define regs
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (fresh-bpf-reg-state)))
  (bpf-verifier-env (apply bpf:regs regs)))

(define (bpf-reg-state-contains? env conc)
  (tnum-contains? (bpf-reg-state-var-off env) conc))

(define (zext_32_to_64 reg)
  (set-bpf-reg-state-var-off! reg (tnum-subreg (bpf-reg-state-var-off reg))))

; Whether concrete state "cpu" is approximated by "env".
(define (bpf-verifier-env-contains? env cpu)
  (define regs (bpf-verifier-env-regs env))
  (define l
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (define r (bpf:idx->reg i))
      (bpf-reg-state-contains? (bpf:@reg-ref regs r) (bpf:reg-ref cpu r))))
  (apply && l))

; Compute new bounds for BPF_ADD
(define (scalar32_min_max_add dst src) (void))
(define (scalar_min_max_add dst src) (void))

; Compute new tnum for BPF_AND
(define (scalar32_min_max_and dst src) (void))
(define (scalar_min_max_and dst src) (void))

; Compute new tnum for BPF_OR
(define (scalar32_min_max_or dst src) (void))
(define (scalar_min_max_or dst src) (void))

(define BPF_CLASS first)
(define BPF_OP second)

(define (adjust_scalar_min_max_vals env insn dst_reg src_reg)
  (define opcode (BPF_OP (bpf:insn-code insn)))
  (define alu32 (! (equal? (BPF_CLASS (bpf:insn-code insn)) 'BPF_ALU64)))

  (case opcode
    [(BPF_ADD)
     (scalar32_min_max_add dst_reg src_reg)
     (scalar_min_max_add dst_reg src_reg)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-add (bpf-reg-state-var-off dst_reg)
                                           (bpf-reg-state-var-off src_reg)))]
    [(BPF_AND)
     (scalar32_min_max_and dst_reg src_reg)
     (scalar_min_max_and dst_reg src_reg)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-and (bpf-reg-state-var-off dst_reg)
                                           (bpf-reg-state-var-off src_reg)))]
    [(BPF_OR)
     (scalar32_min_max_or dst_reg src_reg)
     (scalar_min_max_or dst_reg src_reg)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-or (bpf-reg-state-var-off dst_reg)
                                          (bpf-reg-state-var-off src_reg)))]
    [else (assert #f)])

  (when alu32
    (zext_32_to_64 dst_reg)))

(define (adjust_reg_min_max_vals env insn)
  (define rd (bpf:insn-dst insn))
  (define rs (bpf:insn-src insn))
  (define regs (bpf-verifier-env-regs env))
  (define dst (bpf:@reg-ref regs rd))
  (define src (bpf:@reg-ref regs rs))
  (adjust_scalar_min_max_vals env insn dst src))
