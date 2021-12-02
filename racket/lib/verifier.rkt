#lang rosette

(require "tnum.rkt"
         "common.rkt"
         (prefix-in bpf: serval/bpf))

(provide (all-defined-out))

(struct bpf-reg-state
        (var-off umin-val
                 umax-val
                 smin-val
                 smax-val
                 u32-min-val
                 u32-max-val
                 s32-min-val
                 s32-max-val)
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

; Make an unknown register state
(define (unknown-bpf-reg-state)
  (bpf-reg-state (tnum-unknown 64)
                 (bv 0 64)
                 U64_MAX
                 S64_MIN
                 S64_MAX
                 (bv 0 32)
                 U32_MAX
                 S32_MIN
                 S32_MAX))

; Copy all fields from src to dst.
(define (update-bpf-reg-state! dst src)
  (set-bpf-reg-state-var-off! dst (bpf-reg-state-var-off src))
  (set-bpf-reg-state-umin-val! dst (bpf-reg-state-umin-val src))
  (set-bpf-reg-state-umax-val! dst (bpf-reg-state-umax-val src))
  (set-bpf-reg-state-smin-val! dst (bpf-reg-state-smin-val src))
  (set-bpf-reg-state-smax-val! dst (bpf-reg-state-smax-val src))
  (set-bpf-reg-state-u32-min-val! dst (bpf-reg-state-u32-min-val src))
  (set-bpf-reg-state-u32-max-val! dst (bpf-reg-state-u32-max-val src))
  (set-bpf-reg-state-s32-min-val! dst (bpf-reg-state-s32-min-val src))
  (set-bpf-reg-state-s32-max-val! dst (bpf-reg-state-s32-max-val src)))

(define (bpf-reg-state->json reg)
  (format
   "{\"var_off\": ~a, \"umin_val\": \"~a\", \"umax_val\": \"~a\", \"smin_val\": \"~a\", \"smax_val\": \"~a\", \"u32_min_val\": \"~a\", \"u32_max_val\": \"~a\", \"s32_min_val\": \"~a\", \"s32_max_val\": \"~a\"}"
   (tnum->json (bpf-reg-state-var-off reg))
   (bpf-reg-state-umin-val reg)
   (bpf-reg-state-umax-val reg)
   (bpf-reg-state-smin-val reg)
   (bpf-reg-state-smax-val reg)
   (bpf-reg-state-u32-min-val reg)
   (bpf-reg-state-u32-max-val reg)
   (bpf-reg-state-s32-min-val reg)
   (bpf-reg-state-s32-max-val reg)))

; Make a fresh verifier environment (register mapping)
(define (fresh-bpf-verifier-env)
  (define regs
    (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
      (fresh-bpf-reg-state)))
  (bpf-verifier-env (apply bpf:regs regs)))

; Make a unknown verifier environment that maps all concrete states.
(define (unknown-bpf-verifier-env)
  (define reg (unknown-bpf-reg-state))
  (define regs (make-list bpf:MAX_BPF_JIT_REG reg))
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

(define (bpf-reg-state-invariants reg)
  (define var_off (bpf-reg-state-var-off reg))
  (&& ; If the register is known positive, then the tnum must be similarly bounded.
   (=> (bvsge (bpf-reg-state-smin-val reg) (bv 0 64))
       (bvult (bvor (tnum-mask var_off) (tnum-value var_off)) S64_MIN))
   (=> (bvsge (bpf-reg-state-s32-min-val reg) (bv 0 32))
       (bvult (extract 31 0 (bvor (tnum-mask var_off) (tnum-value var_off))) S32_MIN))))

(define (bpf-verifier-env-invariants env)
  (define regs (bpf-verifier-env-regs env))
  (apply &&
         (for/list ([i (in-range bpf:MAX_BPF_JIT_REG)])
           (bpf-reg-state-invariants (bpf:@reg-ref regs (bpf:idx->reg i))))))

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

(define (__mark_reg_known reg imm)
  (set-bpf-reg-state-var-off! reg (tnum-const imm))
  (set-bpf-reg-state-smin-val! reg imm)
  (set-bpf-reg-state-smax-val! reg imm)
  (set-bpf-reg-state-umin-val! reg imm)
  (set-bpf-reg-state-umax-val! reg imm)

  (set-bpf-reg-state-s32-min-val! reg (extract 31 0 imm))
  (set-bpf-reg-state-s32-max-val! reg (extract 31 0 imm))
  (set-bpf-reg-state-u32-min-val! reg (extract 31 0 imm))
  (set-bpf-reg-state-u32-max-val! reg (extract 31 0 imm)))

(define (__mark_reg32_known reg imm)
  (set-bpf-reg-state-var-off! reg (tnum-const-subreg (bpf-reg-state-var-off reg) imm))
  (set-bpf-reg-state-s32-min-val! reg imm)
  (set-bpf-reg-state-s32-max-val! reg imm)
  (set-bpf-reg-state-u32-min-val! reg imm)
  (set-bpf-reg-state-u32-max-val! reg imm))

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

(define (__update_reg64_bounds reg)
  (define var_off (bpf-reg-state-var-off reg))
  (set-bpf-reg-state-smin-val!
   reg
   (bvsmax (bpf-reg-state-smin-val reg)
           (bvor (tnum-value var_off) (bvand (tnum-mask var_off) S64_MIN))))

  (set-bpf-reg-state-smax-val!
   reg
   (bvsmin (bpf-reg-state-smax-val reg)
           (bvor (tnum-value var_off) (bvand (tnum-mask var_off) S64_MAX))))

  (set-bpf-reg-state-umin-val! reg (bvumax (bpf-reg-state-umin-val reg) (tnum-value var_off)))

  (set-bpf-reg-state-umax-val! reg
                               (bvumin (bpf-reg-state-umax-val reg)
                                       (bvor (tnum-value var_off) (tnum-mask var_off)))))

(define (__update_reg_bounds reg)
  (__update_reg32_bounds reg)
  (__update_reg64_bounds reg))

(define (__reg32_deduce_bounds reg)
  (cond
    [(|| (bvsge (bpf-reg-state-s32-min-val reg) (bv 0 32))
         (bvslt (bpf-reg-state-s32-max-val reg) (bv 0 32)))

     (define newmin (bvumax (bpf-reg-state-s32-min-val reg) (bpf-reg-state-u32-min-val reg)))
     (set-bpf-reg-state-s32-min-val! reg newmin)
     (set-bpf-reg-state-u32-min-val! reg newmin)
     (define newmax (bvumin (bpf-reg-state-s32-max-val reg) (bpf-reg-state-u32-max-val reg)))
     (set-bpf-reg-state-s32-max-val! reg newmax)
     (set-bpf-reg-state-u32-max-val! reg newmax)]

    [(bvsge (bpf-reg-state-u32-max-val reg) (bv 0 32))

     (set-bpf-reg-state-s32-min-val! reg (bpf-reg-state-u32-min-val reg))
     (define newmax (bvumin (bpf-reg-state-s32-max-val reg) (bpf-reg-state-u32-max-val reg)))
     (set-bpf-reg-state-s32-max-val! reg newmax)
     (set-bpf-reg-state-u32-max-val! reg newmax)]

    [(bvslt (bpf-reg-state-u32-min-val reg) (bv 0 32))

     (define newmin (bvumax (bpf-reg-state-s32-min-val reg) (bpf-reg-state-u32-min-val reg)))
     (set-bpf-reg-state-s32-min-val! reg newmin)
     (set-bpf-reg-state-u32-min-val! reg newmin)
     (set-bpf-reg-state-s32-max-val! reg (bpf-reg-state-u32-max-val reg))]))

(define (__reg64_deduce_bounds reg)
  (cond
    [(|| (bvsge (bpf-reg-state-smin-val reg) (bv 0 64))
         (bvslt (bpf-reg-state-smax-val reg) (bv 0 64)))

     (define newmin (bvumax (bpf-reg-state-smin-val reg) (bpf-reg-state-umin-val reg)))
     (set-bpf-reg-state-smin-val! reg newmin)
     (set-bpf-reg-state-umin-val! reg newmin)
     (define newmax (bvumin (bpf-reg-state-smax-val reg) (bpf-reg-state-umax-val reg)))
     (set-bpf-reg-state-smax-val! reg newmax)
     (set-bpf-reg-state-umax-val! reg newmax)]

    [(bvsge (bpf-reg-state-umax-val reg) (bv 0 64))

     (set-bpf-reg-state-smin-val! reg (bpf-reg-state-umin-val reg))
     (define newmax (bvumin (bpf-reg-state-smax-val reg) (bpf-reg-state-umax-val reg)))
     (set-bpf-reg-state-smax-val! reg newmax)
     (set-bpf-reg-state-umax-val! reg newmax)]

    [(bvslt (bpf-reg-state-umin-val reg) (bv 0 64))

     (define newmin (bvumax (bpf-reg-state-smin-val reg) (bpf-reg-state-umin-val reg)))
     (set-bpf-reg-state-smin-val! reg newmin)
     (set-bpf-reg-state-umin-val! reg newmin)
     (set-bpf-reg-state-smax-val! reg (bpf-reg-state-umax-val reg))]))

(define (__reg_deduce_bounds reg)
  (__reg32_deduce_bounds reg)
  (__reg64_deduce_bounds reg))

; Refine tnum based on the unsigned 32- and 64-bit bounds.
(define (__reg_bound_offset reg)
  (define var64_off
    (tnum-intersect (bpf-reg-state-var-off reg)
                    (tnum-range (bpf-reg-state-umin-val reg) (bpf-reg-state-umax-val reg))))
  (define var32_off
    (tnum-intersect (tnum-subreg (bpf-reg-state-var-off reg))
                    (tnum-range (zero-extend (bpf-reg-state-u32-min-val reg) (bitvector 64))
                                (zero-extend (bpf-reg-state-u32-max-val reg) (bitvector 64)))))
  (set-bpf-reg-state-var-off! reg (tnum-or (tnum-clear-subreg var64_off) var32_off)))

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

(define (__mark_reg64_unbounded reg)
  (set-bpf-reg-state-smin-val! reg S64_MIN)
  (set-bpf-reg-state-smax-val! reg S64_MAX)
  (set-bpf-reg-state-umin-val! reg (bv 0 64))
  (set-bpf-reg-state-umax-val! reg U64_MAX))

(define (__mark_reg32_unbounded reg)
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

(define (signed_sub_overflows a b)
  (define N (bitvector-size (type-of a)))
  (define res (bvsub a b))
  (cond
    [(bvslt b (bv 0 N)) (bvslt res a)]
    [else (bvsgt res a)]))

(define signed_sub32_overflows signed_sub_overflows)

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

(define (scalar32_min_max_sub dst src)
  (define smin-val (bpf-reg-state-s32-min-val src))
  (define smax-val (bpf-reg-state-s32-max-val src))
  (define umin-val (bpf-reg-state-u32-min-val src))
  (define umax-val (bpf-reg-state-u32-max-val src))

  (cond
    [(|| (signed_sub32_overflows (bpf-reg-state-s32-min-val dst) smax-val)
         (signed_sub32_overflows (bpf-reg-state-s32-max-val dst) smin-val))
     (set-bpf-reg-state-s32-min-val! dst S32_MIN)
     (set-bpf-reg-state-s32-max-val! dst S32_MAX)]
    [else
     (set-bpf-reg-state-s32-min-val! dst (bvsub (bpf-reg-state-s32-min-val dst) smax-val))
     (set-bpf-reg-state-s32-max-val! dst (bvsub (bpf-reg-state-s32-max-val dst) smin-val))])

  (cond
    [(bvult (bpf-reg-state-u32-min-val dst) umax-val)
     (set-bpf-reg-state-u32-min-val! dst (bv 0 32))
     (set-bpf-reg-state-u32-max-val! dst U32_MAX)]
    [else
     (set-bpf-reg-state-u32-min-val! dst (bvsub (bpf-reg-state-u32-min-val dst) umax-val))
     (set-bpf-reg-state-u32-max-val! dst (bvsub (bpf-reg-state-u32-max-val dst) umin-val))]))

(define (scalar_min_max_sub dst src)
  (define smin-val (bpf-reg-state-smin-val src))
  (define smax-val (bpf-reg-state-smax-val src))
  (define umin-val (bpf-reg-state-umin-val src))
  (define umax-val (bpf-reg-state-umax-val src))

  (cond
    [(|| (signed_sub_overflows (bpf-reg-state-smin-val dst) smax-val)
         (signed_sub_overflows (bpf-reg-state-smax-val dst) smin-val))
     (set-bpf-reg-state-smin-val! dst S64_MIN)
     (set-bpf-reg-state-smax-val! dst S64_MAX)]
    [else
     (set-bpf-reg-state-smin-val! dst (bvsub (bpf-reg-state-smin-val dst) smax-val))
     (set-bpf-reg-state-smax-val! dst (bvsub (bpf-reg-state-smax-val dst) smin-val))])

  (cond
    [(bvult (bpf-reg-state-umin-val dst) umax-val)
     (set-bpf-reg-state-umin-val! dst (bv 0 64))
     (set-bpf-reg-state-umax-val! dst U64_MAX)]
    [else
     (set-bpf-reg-state-umin-val! dst (bvsub (bpf-reg-state-umin-val dst) umax-val))
     (set-bpf-reg-state-umax-val! dst (bvsub (bpf-reg-state-umax-val dst) umin-val))]))

; Compute new tnum for BPF_AND

(define (scalar32_min_max_and dst_reg src_reg)
  (define src_known (tnum-subreg-is-const? (bpf-reg-state-var-off src_reg)))
  (define dst_known (tnum-subreg-is-const? (bpf-reg-state-var-off dst_reg)))
  (define var32_off (tnum-subreg (bpf-reg-state-var-off dst_reg)))
  (define smin_val (bpf-reg-state-s32-min-val src_reg))
  (define umax_val (bpf-reg-state-u32-max-val src_reg))

  (cond
    [(&& src_known dst_known) (__mark_reg32_known dst_reg (extract 31 0 (tnum-value var32_off)))]
    [else
     (set-bpf-reg-state-u32-min-val! dst_reg (extract 31 0 (tnum-value var32_off)))
     (set-bpf-reg-state-u32-max-val! dst_reg (bvumin (bpf-reg-state-u32-max-val dst_reg) umax_val))

     (cond
       [(|| (bvslt (bpf-reg-state-s32-min-val dst_reg) (bv 0 32)) (bvslt smin_val (bv 0 32)))
        (set-bpf-reg-state-s32-min-val! dst_reg S32_MIN)
        (set-bpf-reg-state-s32-max-val! dst_reg S32_MAX)]
       [else
        (set-bpf-reg-state-s32-min-val! dst_reg (bpf-reg-state-u32-min-val dst_reg))
        (set-bpf-reg-state-s32-max-val! dst_reg (bpf-reg-state-u32-max-val dst_reg))])]))

(define (scalar_min_max_and dst_reg src_reg)
  (define src_known (tnum-is-const? (bpf-reg-state-var-off src_reg)))
  (define dst_known (tnum-is-const? (bpf-reg-state-var-off dst_reg)))
  (define smin_val (bpf-reg-state-smin-val src_reg))
  (define umax_val (bpf-reg-state-umax-val src_reg))

  (cond
    [(&& src_known dst_known)
     (__mark_reg_known dst_reg (tnum-value (bpf-reg-state-var-off dst_reg)))]
    [else
     (set-bpf-reg-state-umin-val! dst_reg (tnum-value (bpf-reg-state-var-off dst_reg)))
     (set-bpf-reg-state-umax-val! dst_reg (bvumin (bpf-reg-state-umax-val dst_reg) umax_val))

     (cond
       [(|| (bvslt (bpf-reg-state-smin-val dst_reg) (bv 0 64)) (bvslt smin_val (bv 0 64)))
        (set-bpf-reg-state-smin-val! dst_reg S64_MIN)
        (set-bpf-reg-state-smax-val! dst_reg S64_MAX)]
       [else
        (set-bpf-reg-state-smin-val! dst_reg (bpf-reg-state-umin-val dst_reg))
        (set-bpf-reg-state-smax-val! dst_reg (bpf-reg-state-umax-val dst_reg))])

     (__update_reg_bounds dst_reg)]))

; Compute new tnum/bounds for BPF_OR

(define (scalar32_min_max_or dst_reg src_reg)
  (define src_known (tnum-subreg-is-const? (bpf-reg-state-var-off src_reg)))
  (define dst_known (tnum-subreg-is-const? (bpf-reg-state-var-off dst_reg)))
  (define var32_off (tnum-subreg (bpf-reg-state-var-off dst_reg)))
  (define smin_val (bpf-reg-state-s32-min-val src_reg))
  (define umin_val (bpf-reg-state-u32-min-val src_reg))

  (cond
    [(&& src_known dst_known) (__mark_reg32_known dst_reg (extract 31 0 (tnum-value var32_off)))]
    [else
     (set-bpf-reg-state-u32-min-val! dst_reg (bvumax (bpf-reg-state-u32-min-val dst_reg) umin_val))
     (set-bpf-reg-state-u32-max-val!
      dst_reg
      (extract 31 0 (bvor (tnum-value var32_off) (tnum-mask var32_off))))

     (cond
       [(|| (bvslt (bpf-reg-state-s32-min-val dst_reg) (bv 0 32)) (bvslt smin_val (bv 0 32)))
        (set-bpf-reg-state-s32-min-val! dst_reg S32_MIN)
        (set-bpf-reg-state-s32-max-val! dst_reg S32_MAX)]
       [else
        (set-bpf-reg-state-s32-min-val! dst_reg (bpf-reg-state-u32-min-val dst_reg))
        (set-bpf-reg-state-s32-max-val! dst_reg (bpf-reg-state-u32-max-val dst_reg))])]))

(define (scalar_min_max_or dst_reg src_reg)
  (define src_known (tnum-is-const? (bpf-reg-state-var-off src_reg)))
  (define dst_known (tnum-is-const? (bpf-reg-state-var-off dst_reg)))
  (define smin_val (bpf-reg-state-smin-val src_reg))
  (define umin_val (bpf-reg-state-umin-val src_reg))

  (cond
    [(&& src_known dst_known)
     (__mark_reg_known dst_reg (tnum-value (bpf-reg-state-var-off dst_reg)))]
    [else
     (set-bpf-reg-state-umin-val! dst_reg (bvumax (bpf-reg-state-umin-val dst_reg) umin_val))
     (set-bpf-reg-state-umax-val! dst_reg
                                  (bvor (tnum-value (bpf-reg-state-var-off dst_reg))
                                        (tnum-mask (bpf-reg-state-var-off dst_reg))))

     (cond
       [(|| (bvslt (bpf-reg-state-smin-val dst_reg) (bv 0 64)) (bvslt smin_val (bv 0 64)))
        (set-bpf-reg-state-smin-val! dst_reg S64_MIN)
        (set-bpf-reg-state-smax-val! dst_reg S64_MAX)]
       [else
        (set-bpf-reg-state-smin-val! dst_reg (bpf-reg-state-umin-val dst_reg))
        (set-bpf-reg-state-smax-val! dst_reg (bpf-reg-state-umax-val dst_reg))])

     (__update_reg_bounds dst_reg)]))

; Compute new tnum/bounds for BPF_XOR

(define (scalar32_min_max_xor dst_reg src_reg)
  (define src_known (tnum-subreg-is-const? (bpf-reg-state-var-off src_reg)))
  (define dst_known (tnum-subreg-is-const? (bpf-reg-state-var-off dst_reg)))
  (define var32_off (tnum-subreg (bpf-reg-state-var-off dst_reg)))
  (define smin_val (bpf-reg-state-s32-min-val src_reg))

  (cond
    [(&& src_known dst_known) (__mark_reg32_known dst_reg (extract 31 0 (tnum-value var32_off)))]
    [else
     (set-bpf-reg-state-u32-min-val! dst_reg (extract 31 0 (tnum-value var32_off)))
     (set-bpf-reg-state-u32-max-val!
      dst_reg
      (extract 31 0 (bvor (tnum-value var32_off) (tnum-mask var32_off))))

     (cond
       [(&& (bvsge (bpf-reg-state-s32-min-val dst_reg) (bv 0 32)) (bvsge smin_val (bv 0 32)))
        (set-bpf-reg-state-s32-min-val! dst_reg (bpf-reg-state-u32-min-val dst_reg))
        (set-bpf-reg-state-s32-max-val! dst_reg (bpf-reg-state-u32-max-val dst_reg))]
       [else
        (set-bpf-reg-state-s32-min-val! dst_reg S32_MIN)
        (set-bpf-reg-state-s32-max-val! dst_reg S32_MAX)])]))

(define (scalar_min_max_xor dst_reg src_reg)
  (define src_known (tnum-is-const? (bpf-reg-state-var-off src_reg)))
  (define dst_known (tnum-is-const? (bpf-reg-state-var-off dst_reg)))
  (define smin_val (bpf-reg-state-smin-val src_reg))

  (cond
    [(&& src_known dst_known)
     (__mark_reg_known dst_reg (tnum-value (bpf-reg-state-var-off dst_reg)))]
    [else
     (set-bpf-reg-state-umin-val! dst_reg (tnum-value (bpf-reg-state-var-off dst_reg)))
     (set-bpf-reg-state-umax-val! dst_reg
                                  (bvor (tnum-value (bpf-reg-state-var-off dst_reg))
                                        (tnum-mask (bpf-reg-state-var-off dst_reg))))

     (cond
       [(&& (bvsge (bpf-reg-state-smin-val dst_reg) (bv 0 64)) (bvsge smin_val (bv 0 64)))
        (set-bpf-reg-state-smin-val! dst_reg (bpf-reg-state-umin-val dst_reg))
        (set-bpf-reg-state-smax-val! dst_reg (bpf-reg-state-umax-val dst_reg))]
       [else
        (set-bpf-reg-state-smin-val! dst_reg S64_MIN)
        (set-bpf-reg-state-smax-val! dst_reg S64_MAX)])

     (__update_reg_bounds dst_reg)]))

; Compute new tnum/bounds for BPF_LSH

(define (__scalar32_min_max_lsh dst_reg umin_val umax_val)
  (set-bpf-reg-state-s32-min-val! dst_reg S32_MIN)
  (set-bpf-reg-state-s32-max-val! dst_reg S32_MAX)
  (cond
    [(|| (bvugt umax_val (bv 31 32))
         (bvugt (bpf-reg-state-u32-max-val dst_reg) (bvshl (bv 1 32) (bvsub (bv 31 32) umax_val))))
     (set-bpf-reg-state-u32-min-val! dst_reg (bv 0 32))
     (set-bpf-reg-state-u32-max-val! dst_reg U32_MAX)]
    [else
     (set-bpf-reg-state-u32-min-val! dst_reg (bvshl (bpf-reg-state-u32-min-val dst_reg) umin_val))
     (set-bpf-reg-state-u32-max-val! dst_reg
                                     (bvshl (bpf-reg-state-u32-max-val dst_reg) umax_val))]))

(define (__scalar64_min_max_lsh dst_reg umin_val umax_val)
  (cond
    [(&& (equal? umin_val (bv 32 64))
         (equal? umax_val (bv 32 64))
         (bvsge (bpf-reg-state-s32-max-val dst_reg) (bv 0 32)))
     (set-bpf-reg-state-smax-val!
      dst_reg
      (bvshl (sign-extend (bpf-reg-state-s32-max-val dst_reg) (bitvector 64)) (bv 32 64)))]
    [else (set-bpf-reg-state-smax-val! dst_reg S64_MAX)])

  (cond
    [(&& (equal? umin_val (bv 32 64))
         (equal? umax_val (bv 32 64))
         (bvsge (bpf-reg-state-s32-min-val dst_reg) (bv 0 32)))
     (set-bpf-reg-state-smin-val!
      dst_reg
      (bvshl (sign-extend (bpf-reg-state-s32-min-val dst_reg) (bitvector 64)) (bv 32 64)))]
    [else (set-bpf-reg-state-smin-val! dst_reg S64_MIN)])

  (cond
    [(bvugt (bpf-reg-state-umax-val dst_reg) (bvshl (bv 1 64) (bvsub (bv 63 64) umax_val)))
     (set-bpf-reg-state-umin-val! dst_reg (bv 0 64))
     (set-bpf-reg-state-umax-val! dst_reg U64_MAX)]
    [else
     (set-bpf-reg-state-umin-val! dst_reg (bvshl (bpf-reg-state-umin-val dst_reg) umin_val))
     (set-bpf-reg-state-umax-val! dst_reg (bvshl (bpf-reg-state-umax-val dst_reg) umax_val))]))

(define (scalar32_min_max_lsh dst_reg src_reg)
  (define umax_val (bpf-reg-state-u32-max-val src_reg))
  (define umin_val (bpf-reg-state-u32-min-val src_reg))

  (define dst_subreg (tnum-subreg (bpf-reg-state-var-off dst_reg)))
  (define src_subreg (tnum-subreg (bpf-reg-state-var-off src_reg)))

  (__scalar32_min_max_lsh dst_reg umin_val umax_val)
  (set-bpf-reg-state-var-off! dst_reg (tnum-subreg (tnum-shl dst_subreg src_subreg 32)))

  (__mark_reg64_unbounded dst_reg)
  (__update_reg32_bounds dst_reg))

(define (scalar_min_max_lsh dst_reg src_reg)
  (define umax_val (bpf-reg-state-umax-val src_reg))
  (define umin_val (bpf-reg-state-umin-val src_reg))

  (__scalar64_min_max_lsh dst_reg umin_val umax_val)
  (__scalar32_min_max_lsh dst_reg (extract 31 0 umin_val) (extract 31 0 umax_val))

  (set-bpf-reg-state-var-off!
   dst_reg
   (tnum-shl (bpf-reg-state-var-off dst_reg) (bpf-reg-state-var-off src_reg) 64))

  (__update_reg_bounds dst_reg))

(define (scalar32_min_max_rsh dst_reg src_reg)
  (define dst_subreg (tnum-subreg (bpf-reg-state-var-off dst_reg)))
  (define src_subreg (tnum-subreg (bpf-reg-state-var-off src_reg)))
  (define umax_val (bpf-reg-state-u32-max-val src_reg))
  (define umin_val (bpf-reg-state-u32-min-val src_reg))

  (set-bpf-reg-state-s32-min-val! dst_reg S32_MIN)
  (set-bpf-reg-state-s32-max-val! dst_reg S32_MAX)

  (set-bpf-reg-state-var-off! dst_reg (tnum-lshr dst_subreg src_subreg 32))
  (set-bpf-reg-state-u32-min-val! dst_reg (bvlshr (bpf-reg-state-u32-min-val dst_reg) umax_val))
  (set-bpf-reg-state-u32-max-val! dst_reg (bvlshr (bpf-reg-state-u32-max-val dst_reg) umin_val))

  (__mark_reg64_unbounded dst_reg)
  (__update_reg32_bounds dst_reg))

(define (scalar_min_max_rsh dst_reg src_reg)
  (define umax_val (bpf-reg-state-umax-val src_reg))
  (define umin_val (bpf-reg-state-umin-val src_reg))

  (set-bpf-reg-state-smin-val! dst_reg S64_MIN)
  (set-bpf-reg-state-smax-val! dst_reg S64_MAX)

  (set-bpf-reg-state-var-off!
   dst_reg
   (tnum-lshr (bpf-reg-state-var-off dst_reg) (bpf-reg-state-var-off src_reg) 64))
  (set-bpf-reg-state-umin-val! dst_reg (bvlshr (bpf-reg-state-umin-val dst_reg) umax_val))
  (set-bpf-reg-state-umax-val! dst_reg (bvlshr (bpf-reg-state-umax-val dst_reg) umin_val))

  (__mark_reg32_unbounded dst_reg)
  (__update_reg_bounds dst_reg))

(define (scalar32_min_max_arsh dst_reg src_reg)
  (define umin_val (bpf-reg-state-u32-min-val src_reg))

  ; Assume umin_val and umax_val of src_reg are equal, i.e., that it is a constant.
  (assume (equal? (bpf-reg-state-u32-min-val src_reg) (bpf-reg-state-u32-max-val src_reg)))

  (set-bpf-reg-state-s32-min-val! dst_reg (bvashr (bpf-reg-state-s32-min-val dst_reg) umin_val))
  (set-bpf-reg-state-s32-max-val! dst_reg (bvashr (bpf-reg-state-s32-max-val dst_reg) umin_val))

  (set-bpf-reg-state-var-off! dst_reg
                              (tnum-arshift (tnum-subreg (bpf-reg-state-var-off dst_reg))
                                            (zero-extend umin_val (bitvector 64))
                                            32))

  (set-bpf-reg-state-u32-min-val! dst_reg (bv 0 32))
  (set-bpf-reg-state-u32-max-val! dst_reg U32_MAX)

  (__mark_reg64_unbounded dst_reg)
  (__update_reg32_bounds dst_reg))

(define (scalar_min_max_arsh dst_reg src_reg)
  (define umin_val (bpf-reg-state-umin-val src_reg))

  ; Assume umin_val and umax_val of src_reg are equal, i.e., that it is a constant.
  (assume (equal? (bpf-reg-state-umin-val src_reg) (bpf-reg-state-umax-val src_reg)))

  (set-bpf-reg-state-smin-val! dst_reg (bvashr (bpf-reg-state-smin-val dst_reg) umin_val))
  (set-bpf-reg-state-smax-val! dst_reg (bvashr (bpf-reg-state-smax-val dst_reg) umin_val))

  (set-bpf-reg-state-var-off! dst_reg (tnum-arshift (bpf-reg-state-var-off dst_reg) umin_val 64))

  (set-bpf-reg-state-umin-val! dst_reg (bv 0 64))
  (set-bpf-reg-state-umax-val! dst_reg U64_MAX)

  (__mark_reg32_unbounded dst_reg)
  (__update_reg_bounds dst_reg))

(define BPF_CLASS first)
(define BPF_OP second)

(define (adjust_scalar_min_max_vals env insn dst_reg src_reg)
  (define regs (bpf-verifier-env-regs env))
  (define opcode (BPF_OP (bpf:insn-code insn)))
  (define insn_bitness
    (if (equal? (BPF_CLASS (bpf:insn-code insn)) 'BPF_ALU64) (bv 64 64) (bv 32 64)))
  (define alu32 (! (equal? (BPF_CLASS (bpf:insn-code insn)) 'BPF_ALU64)))
  (define smin_val (bpf-reg-state-smin-val src_reg))
  (define smax_val (bpf-reg-state-smax-val src_reg))
  (define umin_val (bpf-reg-state-umin-val src_reg))
  (define umax_val (bpf-reg-state-umax-val src_reg))

  (case opcode
    [(BPF_MOV) (update-bpf-reg-state! dst_reg src_reg)]

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
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-and (bpf-reg-state-var-off dst_reg)
                                           (bpf-reg-state-var-off src_reg)))
     (scalar32_min_max_and dst_reg src_reg)
     (scalar_min_max_and dst_reg src_reg)]

    [(BPF_OR)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-or (bpf-reg-state-var-off dst_reg)
                                          (bpf-reg-state-var-off src_reg)))
     (scalar32_min_max_or dst_reg src_reg)
     (scalar_min_max_or dst_reg src_reg)]

    [(BPF_XOR)
     (set-bpf-reg-state-var-off! dst_reg
                                 (tnum-xor (bpf-reg-state-var-off dst_reg)
                                           (bpf-reg-state-var-off src_reg)))
     (scalar32_min_max_xor dst_reg src_reg)
     (scalar_min_max_xor dst_reg src_reg)]

    [(BPF_LSH) (cond
                 [(bvuge umax_val insn_bitness) (mark_reg_unknown env regs (bpf:insn-dst insn))]
                 [alu32 (scalar32_min_max_lsh dst_reg src_reg)]
                 [else (scalar_min_max_lsh dst_reg src_reg)])]

    [(BPF_RSH) (cond
                 [(bvuge umax_val insn_bitness) (mark_reg_unknown env regs (bpf:insn-dst insn))]
                 [alu32 (scalar32_min_max_rsh dst_reg src_reg)]
                 [else (scalar_min_max_rsh dst_reg src_reg)])]

    [(BPF_ARSH) (cond
                  [(bvuge umax_val insn_bitness) (mark_reg_unknown env regs (bpf:insn-dst insn))]
                  [alu32 (scalar32_min_max_arsh dst_reg src_reg)]
                  [else (scalar_min_max_arsh dst_reg src_reg)])]

    [else (assert #f)])

  (when alu32
    (zext_32_to_64 dst_reg))

  (when (! (equal? opcode 'BPF_MOV))
    (__update_reg_bounds dst_reg)
    (__reg_deduce_bounds dst_reg)
    (__reg_bound_offset dst_reg)))

(define (adjust_reg_min_max_vals env insn)
  (define rd (bpf:insn-dst insn))
  (define rs (bpf:insn-src insn))
  (define regs (bpf-verifier-env-regs env))
  (define dst (bpf:@reg-ref regs rd))
  (define src (bpf:@reg-ref regs rs))
  (adjust_scalar_min_max_vals env insn dst src))
