#lang rosette

(require "pow.rkt"
         serval/lib/debug)

(provide (all-defined-out))

(struct tnum (value mask)
  #:transparent)

; A tnum is valid if there is no bit set in the value and the mask.
(define (tnum-valid? t) (bvzero? (bvand (tnum-value t) (tnum-mask t))))

; The unknown tnum of width n.
(define (tnum-unknown n) (tnum (bv 0 n) (bvnot (bv 0 n))))

; Whether some constant bitvector is represented by the tnum t.
(define (tnum-contains? t c)
  (define v (tnum-value t))
  (define mu (tnum-mask t))

  (define ok (bvor mu (bvnot (bvxor v c))))
  (bvzero? (bvnot ok)))

; Make a symbolic expression representing the same set of bitvectors as a tnum
; Returns the symbolic expression and a list of symbolics involved in the representation,
; that does not include symbolics from the tnum itself.
(define (tnum->symbolic t)
  (define-symbolic* c (type-of (tnum-value t)))
  ; Mask out bits not set in the tnum mask
  (set! c (bvand c (tnum-mask t)))
  ; Take value bits from tnum
  (values (bvor c (tnum-value t)) (list c)))

; Construct a tnum representing a single bitvector.
(define (tnum-const c) (tnum c (bvxor c c)))

; Returns a fresh, symbolic tnum of size n, assumed to be valid.
(define (fresh-tnum n)
  (define-symbolic* value mask (bitvector n))
  (define t (tnum value mask))
  (assume (tnum-valid? t))
  t)

; Shift a tnum left by a constant
(define (tnum-lshift a shift) (tnum (bvshl (tnum-value a) shift) (bvshl (tnum-mask a) shift)))

; Shift a tnum right (logical) by a constant
(define (tnum-rshift a shift) (tnum (bvlshr (tnum-value a) shift) (bvlshr (tnum-mask a) shift)))

; Intersect two tnums. Sets value bit to 1 if disagreement.
(define (tnum-intersect a b)
  (define v (bvor (tnum-value a) (tnum-value b)))
  (define mu (bvand (tnum-mask a) (tnum-mask b)))
  (tnum (bvand v (bvnot mu)) mu))

; Union two tnums.
(define (tnum-union a b)
  (define mu (bvor (tnum-mask a) (tnum-mask b) (bvxor (tnum-value a) (tnum-value b))))
  (tnum (bvand (tnum-value a) (bvnot mu)) mu))

; Bitwise AND of two tnums.
(define (tnum-and a b)
  (define alpha (bvor (tnum-value a) (tnum-mask a)))
  (define beta (bvor (tnum-value b) (tnum-mask b)))
  (define v (bvand (tnum-value a) (tnum-value b)))
  (tnum v (bvand alpha beta (bvnot v))))

; Arithmetic ADD of two tnums.
(define (tnum-add a b)
  (define sm (bvadd (tnum-mask a) (tnum-mask b)))
  (define sv (bvadd (tnum-value a) (tnum-value b)))
  (define sigma (bvadd sm sv))
  (define chi (bvxor sigma sv))
  (define mu (bvor chi (tnum-mask a) (tnum-mask b)))
  (tnum (bvand sv (bvnot mu)) mu))

; Left shift a tnum by a tnum.
(define (tnum-shl a b)
  (define N (bitvector-size (type-of (tnum-value a))))
  (assert (is-pow2? N))
  (define amt (bv 1 N))

  ; Use only the lower log2(N) bits of b.
  (set! b (tnum-and b (tnum-const (bvsub1 (bv N N)))))

  (define (loop fuel)
    (cond
      [(zero? fuel) (bug-assert #f)]
      [(! (bvzero? (bvor (tnum-value b) (tnum-mask b))))

       (when (! (bvzero? (bvand (tnum-mask b) (bv 1 N))))
         (set! a (tnum-union a (tnum-lshift a amt))))

       (when (! (bvzero? (bvand (tnum-value b) (bv 1 N))))
         (set! a (tnum-lshift a amt)))

       (set! amt (bvshl amt (bv 1 N)))
       (set! b (tnum-rshift b (bv 1 N)))
       (loop (sub1 fuel))]))
  (loop (add1 (log2 N)))
  a)

; Right shift (logical) a tnum by a tnum.
(define (tnum-lshr a b)
  (define N (bitvector-size (type-of (tnum-value a))))
  (assert (is-pow2? N))
  (define amt (bv 1 N))

  ; Use only the lower log2(N) bits of b.
  (set! b (tnum-and b (tnum-const (bvsub1 (bv N N)))))

  (define (loop fuel)
    (cond
      [(zero? fuel) (bug-assert #f)]
      [(! (bvzero? (bvor (tnum-value b) (tnum-mask b))))

       (when (! (bvzero? (bvand (tnum-mask b) (bv 1 N))))
         (set! a (tnum-union a (tnum-rshift a amt))))

       (when (! (bvzero? (bvand (tnum-value b) (bv 1 N))))
         (set! a (tnum-rshift a amt)))

       (set! amt (bvshl amt (bv 1 N)))
       (set! b (tnum-rshift b (bv 1 N)))
       (loop (sub1 fuel))]))
  (loop (add1 (log2 N)))
  a)
