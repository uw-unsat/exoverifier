#lang rosette

(require "pow.rkt"
         "common.rkt"
         serval/lib/debug
         serval/lib/bvarith)

(provide (all-defined-out))

(struct tnum (value mask) #:transparent)

; A tnum is valid if there is no bit set in the value and the mask.
(define (tnum-valid? t)
  (bvzero? (bvand (tnum-value t) (tnum-mask t))))

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

(define (tnum-range min max)
  (define N (bitvector-size (type-of min)))
  (define chi (bvxor min max))
  (define bits (fls chi))

  (cond
    [(bvugt bits (bv (sub1 N) N)) (tnum-unknown N)]
    [else
     (define delta (bvsub1 (bvshl (bv 1 N) bits)))
     (tnum (bvand min (bvnot delta)) delta)]))

; Shift a tnum left by a constant
(define (tnum-lshift a shift)
  (tnum (bvshl (tnum-value a) shift) (bvshl (tnum-mask a) shift)))

; Shift a tnum right (logical) by a constant
(define (tnum-rshift a shift)
  (tnum (bvlshr (tnum-value a) shift) (bvlshr (tnum-mask a) shift)))

; Shift a tnum right (arithmetic) by a constant
(define (tnum-arshift a shift bitness)
  (define lomask (trunc bitness (tnum-mask a)))
  (define lovalue (trunc bitness (tnum-value a)))
  (define loshift (trunc bitness shift))

  (tnum (zero-extend (bvashr lovalue loshift) (type-of shift))
        (zero-extend (bvashr lomask loshift) (type-of shift))))

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

; Bitwise OR of two tnums.
(define (tnum-or a b)
  (define v (bvor (tnum-value a) (tnum-value b)))
  (define mu (bvor (tnum-mask a) (tnum-mask b)))
  (tnum v (bvand mu (bvnot v))))

; Bitwise XOR of two tnums.
(define (tnum-xor a b)
  (define v (bvxor (tnum-value a) (tnum-value b)))
  (define mu (bvor (tnum-mask a) (tnum-mask b)))
  (tnum (bvand v (bvnot mu)) mu))

; Arithmetic ADD of two tnums.
(define (tnum-add a b)
  (define sm (bvadd (tnum-mask a) (tnum-mask b)))
  (define sv (bvadd (tnum-value a) (tnum-value b)))
  (define sigma (bvadd sm sv))
  (define chi (bvxor sigma sv))
  (define mu (bvor chi (tnum-mask a) (tnum-mask b)))
  (tnum (bvand sv (bvnot mu)) mu))

; Left shift a tnum by a tnum.
(define (tnum-shl a b bitness)
  (define N (bitvector-size (type-of (tnum-value a))))
  (assert (is-pow2? bitness))
  (define amt (bv 1 N))

  ; Use only the lower log2(N) bits of b.
  (set! b (tnum-and b (tnum-const (bvsub1 (bv bitness N)))))

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
(define (tnum-lshr a b bitness)
  (define N (bitvector-size (type-of (tnum-value a))))
  (assert (is-pow2? bitness))
  (define amt (bv 1 N))

  ; Use only the lower log2(N) bits of b.
  (set! b (tnum-and b (tnum-const (bvsub1 (bv bitness N)))))

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

; Right shift (arithmetic) a tnum by a tnum.
(define (tnum-ashr a b bitness)
  (define N (bitvector-size (type-of (tnum-value a))))
  (assert (is-pow2? bitness))
  (define amt (bv 1 N))

  ; Use only the lower log2(N) bits of b.
  (set! b (tnum-and b (tnum-const (bvsub1 (bv bitness N)))))

  (define (loop fuel)
    (cond
      [(zero? fuel) (bug-assert #f)]
      [(! (bvzero? (bvor (tnum-value b) (tnum-mask b))))

       (when (! (bvzero? (bvand (tnum-mask b) (bv 1 N))))
         (set! a (tnum-union a (tnum-arshift a amt bitness))))

       (when (! (bvzero? (bvand (tnum-value b) (bv 1 N))))
         (set! a (tnum-arshift a amt bitness)))

       (set! amt (bvshl amt (bv 1 N)))
       (set! b (tnum-rshift b (bv 1 N)))
       (loop (sub1 fuel))]))
  (loop (add1 (log2 N)))
  a)

(define (tnum-in a b)
  (cond
    [(! (bvzero? (bvand (tnum-mask b) (bvnot (tnum-mask a))))) #f]
    [else
     (define b-value2 (bvand (tnum-value b) (bvnot (tnum-mask a))))
     (equal? (tnum-value a) b-value2)]))
