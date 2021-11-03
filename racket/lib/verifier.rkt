#lang rosette

(require "tnum.rkt"
         (prefix-in bpf: serval/bpf))

(provide (all-defined-out))

(struct bpf-reg-state
        (var-off umin-val umax-val smin-val smax-val u32-min-val u32-max-val s32-min-val s32-max-val)
  #:mutable
  #:transparent)

(struct bpf-verifier-env (regs) #:mutable #:transparent)

; Make a fresh register state
(define (fresh-bpf-reg-state)
  (define-symbolic* umin-val umax-val smin-val smax-val (bitvector 64))
  (define-symbolic* u32-min-val u32-max-val s32-min-val s32-max-val (bitvector 32))
  (bpf-reg-state (fresh-tnum 64)
                 umin-val
                 umax-val
                 smin-val
                 smax-val
                 u32-min-val
                 u32-max-val
                 s32-min-val
                 s32-max-val))

; Make a fresh verifier environment (register mapping)
(define (fresh-bpf-verifier-env)
  (define regs
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (fresh-bpf-reg-state)))
  (bpf-verifier-env (apply bpf:regs regs)))

(define (bpf-reg-state-contains? env conc)
  (define low32 (extract 31 0 conc))

  (&& (tnum-contains? (bpf-reg-state-var-off env) conc)
      (bvule (bpf-reg-state-umin-val env) conc)
      (bvule conc (bpf-reg-state-umax-val env))
      (bvsle (bpf-reg-state-smin-val env) conc)
      (bvsle conc (bpf-reg-state-smax-val env))
      (bvule (bpf-reg-state-u32-min-val env) low32)
      (bvule low32 (bpf-reg-state-u32-max-val env))
      (bvsle (bpf-reg-state-s32-min-val env) low32)
      (bvsle low32 (bpf-reg-state-s32-max-val env))))

(define S64_MIN (bvshl (bv 1 64) (bv 63 64)))
(define S64_MAX (bvnot S64_MIN))
(define U64_MAX (bv -1 64))
(define S32_MIN (bvshl (bv 1 32) (bv 31 32)))
(define S32_MAX (bvnot S32_MIN))
(define U32_MAX (bv -1 32))

(define (__reg_assign_32_into_64 reg)
  (set-bpf-reg-state-umin-val! reg (zero-extend (bpf-reg-state-u32-min-val reg) (bitvector 64)))
  (set-bpf-reg-state-umax-val! reg (zero-extend (bpf-reg-state-u32-max-val reg) (bitvector 64)))

  (cond
    [(&& (bvsge (bpf-reg-state-s32-min-val reg) (bv 0 32))
         (bvsge (bpf-reg-state-s32-max-val reg) (bv 0 32)))
     (set-bpf-reg-state-smax-val! reg (sign-extend (bpf-reg-state-s32-max-val reg) (bitvector 64)))]
    [else (set-bpf-reg-state-smax-val! reg (zero-extend U32_MAX (bitvector 64)))])

  (cond
    [(bvsge (bpf-reg-state-s32-min-val reg) (bv 0 32))
     (set-bpf-reg-state-smin-val! reg (sign-extend (bpf-reg-state-s32-min-val reg) (bitvector 64)))]
    [else (set-bpf-reg-state-smin-val! reg (bv 0 64))]))

(define (zext_32_to_64 reg)
  (set-bpf-reg-state-var-off! reg (tnum-subreg (bpf-reg-state-var-off reg)))
  (__reg_assign_32_into_64 reg))

(define (__update_reg32_bounds reg)
  (define var32_off (tnum-subreg (bpf-reg-state-var-off reg)))

  (set-bpf-reg-state-s32-min-val!
   reg
   (bvsmax (bpf-reg-state-s32-min-val reg)
           (extract 31
                    0
                    (bvor (tnum-value var32_off)
                          (bvand (tnum-mask var32_off) (sign-extend S32_MIN (bitvector 64)))))))
  (set-bpf-reg-state-s32-max-val!
   reg
   (bvsmin (bpf-reg-state-s32-max-val reg)
           (extract 31
                    0
                    (bvor (tnum-value var32_off)
                          (bvand (tnum-mask var32_off) (sign-extend S32_MAX (bitvector 64)))))))

  (set-bpf-reg-state-u32-min-val! reg
                                  (bvumax (bpf-reg-state-u32-min-val reg)
                                          (extract 31 0 (tnum-value var32_off))))
  (set-bpf-reg-state-u32-max-val!
   reg
   (bvumin (bpf-reg-state-u32-max-val reg)
           (extract 31 0 (bvor (tnum-value var32_off) (tnum-mask var32_off))))))

(define (__update_reg64_bounds reg) (void))

(define (__update_reg_bounds reg)
  (__update_reg32_bounds reg)
  (__update_reg64_bounds reg))

(define (__reg_deduce_bounds reg) (void))

(define (__reg_bound_offset reg) (void))

; Throw away bounds information for a register
(define (__mark_reg_unbounded reg)
  (set-bpf-reg-state-smin-val! reg S64_MIN)
  (set-bpf-reg-state-smax-val! reg S64_MAX)
  (set-bpf-reg-state-umin-val! reg (bv 0 64))
  (set-bpf-reg-state-umax-val! reg U64_MAX)
  (set-bpf-reg-state-s32-min-val! reg S32_MIN)
  (set-bpf-reg-state-s32-max-val! reg S32_MAX)
  (set-bpf-reg-state-u32-min-val! reg (bv 0 32))
  (set-bpf-reg-state-u32-max-val! reg U32_MAX))

; Mark a regiser wholly unknown by clearing bounds and tnum.
(define (mark_reg_unknown env regs reg)
  (define regstate (bpf:@reg-ref regs reg))
  (set-bpf-reg-state-var-off! regstate (tnum-unknown 64))
  (__mark_reg_unbounded regstate))

(define (signed_add_overflows a b)
  (define N (bitvector-size (type-of a)))
  (define res (bvadd a b))
  (cond
    [(bvslt b (bv 0 N)) (bvsgt res a)]
    [else (bvslt res a)]))

; NB: "signed_add_overflows" works with any bitwidth.
(define signed_add32_overflows signed_add_overflows)

; Whether concrete state "cpu" is approximated by "env".
(define (bpf-verifier-env-contains? env cpu)
  (define regs (bpf-verifier-env-regs env))
  (define l
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (define r (bpf:idx->reg i))
      (bpf-reg-state-contains? (bpf:@reg-ref regs r) (bpf:reg-ref cpu r))))
  (apply && l))

; Compute new bounds for BPF_ADD
(define (scalar_min_max_add dst src)
  (define smin-val (bpf-reg-state-smin-val src))
  (define smax-val (bpf-reg-state-smax-val src))
  (define umin-val (bpf-reg-state-umin-val src))
  (define umax-val (bpf-reg-state-umax-val src))

  (cond
    [(|| (signed_add_overflows (bpf-reg-state-smin-val dst) smin-val)
         (signed_add_overflows (bpf-reg-state-smax-val dst) smax-val))
     (set-bpf-reg-state-smin-val! dst S64_MIN)
     (set-bpf-reg-state-smax-val! dst S64_MAX)]
    [else
     (set-bpf-reg-state-smin-val! dst (bvadd (bpf-reg-state-smin-val dst) smin-val))
     (set-bpf-reg-state-smax-val! dst (bvadd (bpf-reg-state-smax-val dst) smax-val))])

  (cond
    [(|| (bvult (bvadd (bpf-reg-state-umin-val dst) umin-val) umin-val)
         (bvult (bvadd (bpf-reg-state-umax-val dst) umax-val) umax-val))
     (set-bpf-reg-state-umin-val! dst (bv 0 64))
     (set-bpf-reg-state-umax-val! dst U64_MAX)]
    [else
     (set-bpf-reg-state-umin-val! dst (bvadd (bpf-reg-state-umin-val dst) umin-val))
     (set-bpf-reg-state-umax-val! dst (bvadd (bpf-reg-state-umax-val dst) umax-val))]))

(define (scalar32_min_max_add dst src)
  (define smin-val (bpf-reg-state-s32-min-val src))
  (define smax-val (bpf-reg-state-s32-max-val src))
  (define umin-val (bpf-reg-state-u32-min-val src))
  (define umax-val (bpf-reg-state-u32-max-val src))

  (cond
    [(|| (signed_add32_overflows (bpf-reg-state-s32-min-val dst) smin-val)
         (signed_add32_overflows (bpf-reg-state-s32-max-val dst) smax-val))
     (set-bpf-reg-state-s32-min-val! dst S32_MIN)
     (set-bpf-reg-state-s32-max-val! dst S32_MAX)]
    [else
     (set-bpf-reg-state-s32-min-val! dst (bvadd (bpf-reg-state-s32-min-val dst) smin-val))
     (set-bpf-reg-state-s32-max-val! dst (bvadd (bpf-reg-state-s32-max-val dst) smax-val))])

  (cond
    [(|| (bvult (bvadd (bpf-reg-state-u32-min-val dst) umin-val) umin-val)
         (bvult (bvadd (bpf-reg-state-u32-max-val dst) umax-val) umax-val))
     (set-bpf-reg-state-u32-min-val! dst (bv 0 32))
     (set-bpf-reg-state-u32-max-val! dst U32_MAX)]
    [else
     (set-bpf-reg-state-u32-min-val! dst (bvadd (bpf-reg-state-u32-min-val dst) umin-val))
     (set-bpf-reg-state-u32-max-val! dst (bvadd (bpf-reg-state-u32-max-val dst) umax-val))]))

; Compute new bounds for BPF_SUB
(define (scalar32_min_max_sub dst src) (__mark_reg_unbounded dst))
(define (scalar_min_max_sub dst src) (__mark_reg_unbounded dst))

; Compute new tnum for BPF_AND
(define (scalar32_min_max_and dst src) (__mark_reg_unbounded dst))
(define (scalar_min_max_and dst src) (__mark_reg_unbounded dst))

; Compute new tnum for BPF_OR
(define (scalar32_min_max_or dst src) (__mark_reg_unbounded dst))
(define (scalar_min_max_or dst src) (__mark_reg_unbounded dst))

; Compute new tnum for BPF_XOR
(define (scalar32_min_max_xor dst src) (__mark_reg_unbounded dst))
(define (scalar_min_max_xor dst src) (__mark_reg_unbounded dst))

(define BPF_CLASS first)
(define BPF_OP second)

(define (adjust_scalar_min_max_vals env insn dst_reg src_reg)
  (define opcode (BPF_OP (bpf:insn-code insn)))
  (define insn_bitness
    (if (equal? (BPF_CLASS (bpf:insn-code insn)) 'BPF_ALU64) (bv 64 64) (bv 32 64)))
  (define alu32 (! (equal? (BPF_CLASS (bpf:insn-code insn)) 'BPF_ALU64)))
  (define smin-val (bpf-reg-state-smin-val src_reg))
  (define smax-val (bpf-reg-state-smax-val src_reg))
  (define umin-val (bpf-reg-state-umin-val src_reg))
  (define umax-val (bpf-reg-state-umax-val src_reg))

  (case opcode
    [(BPF_ADD)
     (scalar32_min_max_add dst_reg src_reg)
     (scalar_min_max_add dst_reg src_reg)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-add (bpf-reg-state-var-off dst_reg)
                                           (bpf-reg-state-var-off src_reg)))]
    [(BPF_SUB)
     (scalar32_min_max_sub dst_reg src_reg)
     (scalar_min_max_sub dst_reg src_reg)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-sub (bpf-reg-state-var-off dst_reg)
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
    [(BPF_XOR)
     (scalar32_min_max_xor dst_reg src_reg)
     (scalar_min_max_xor dst_reg src_reg)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-xor (bpf-reg-state-var-off dst_reg)
                                           (bpf-reg-state-var-off src_reg)))]
    [else (assert #f)])

  (when alu32
    (zext_32_to_64 dst_reg))

  (__update_reg_bounds dst_reg)
  (__reg_deduce_bounds dst_reg)
  (__reg_bound_offset dst_reg))

(define (adjust_reg_min_max_vals env insn)
  (define rd (bpf:insn-dst insn))
  (define rs (bpf:insn-src insn))
  (define regs (bpf-verifier-env-regs env))
  (define dst (bpf:@reg-ref regs rd))
  (define src (bpf:@reg-ref regs rs))
  (adjust_scalar_min_max_vals env insn dst src))
