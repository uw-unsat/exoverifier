#lang rosette

(require "../lib/tnum.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/unittest)

(define N (make-parameter 64))

(define (test-unknown n)
  (define unknown (tnum-unknown n))

  (define-symbolic* c (bitvector n))

  (bug-assert (tnum-valid? unknown) #:msg "Unknown tnum must be valid")
  (bug-assert (tnum-contains? unknown c) #:msg "Unknown should contain all tnums"))

(define (test-const n)
  (define-symbolic* c c2 (bitvector n))
  (define const (tnum-const c))

  (bug-assert (tnum-valid? const) #:msg "tnum-const must return valid tnum")
  (bug-assert (<=> (tnum-contains? const c2) (equal? c c2))
              #:msg "tnum-const contains only the constant"))

(define (test-intersect n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-intersect a b))
  (bug-assert (tnum-valid? c) #:msg "intersection must be valid")

  (define-symbolic* v (bitvector n))
  (bug-assert (=> (&& (tnum-contains? a v) (tnum-contains? b v)) (tnum-contains? c v))))

(define (test-union n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-union a b))
  (bug-assert (tnum-valid? c) #:msg "union must be valid")

  (define-symbolic* v (bitvector n))
  (bug-assert (=> (|| (tnum-contains? a v) (tnum-contains? b v)) (tnum-contains? c v))))

(define (test-and n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-and a b))
  (bug-assert (tnum-valid? c) #:msg "and must be valid")

  (define-symbolic* x y (bitvector n))
  (bug-assert (=> (&& (tnum-contains? a x) (tnum-contains? b y)) (tnum-contains? c (bvand x y)))))

(define (test-add n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-add a b))
  (bug-assert (tnum-valid? c) #:msg "add must be valid")

  (define-symbolic* x y (bitvector n))
  (bug-assert (=> (&& (tnum-contains? a x) (tnum-contains? b y)) (tnum-contains? c (bvadd x y)))))

(define (test-shl n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-shl a b))
  (bug-assert (tnum-valid? c) #:msg "shl must be valid")

  (define-symbolic* x y (bitvector n))
  ; Assume shift amount is valid
  (assume (bvult y (bv n n)))
  (bug-assert (=> (&& (tnum-contains? a x) (tnum-contains? b y)) (tnum-contains? c (bvshl x y)))))

(define (test-lshr n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-lshr a b))
  (bug-assert (tnum-valid? c) #:msg "lshr must be valid")

  (define-symbolic* x y (bitvector n))
  ; Assume shift amount is valid
  (assume (bvult y (bv n n)))
  (bug-assert (=> (&& (tnum-contains? a x) (tnum-contains? b y)) (tnum-contains? c (bvlshr x y)))))

(define (test-lshift n)
  (define a (fresh-tnum n))
  (define-symbolic* shift (bitvector n))
  (define b (tnum-lshift a shift))
  (bug-assert (tnum-valid? b) #:msg "add must be valid")

  (define-symbolic* x (bitvector n))
  (bug-assert (=> (tnum-contains? a x) (tnum-contains? b (bvshl x shift)))))

(define (test-rshift n)
  (define a (fresh-tnum n))
  (define-symbolic* shift (bitvector n))
  (define b (tnum-rshift a shift))
  (bug-assert (tnum-valid? b) #:msg "add must be valid")

  (define-symbolic* x (bitvector n))
  (bug-assert (=> (tnum-contains? a x) (tnum-contains? b (bvlshr x shift)))))

(define tnum-tests
  (test-suite+ "Tests for tnum"
               (test-case+ "Test constant tnums" (test-const (N)))
               (test-case+ "Test intersection of tnums" (test-intersect (N)))
               (test-case+ "Test union of tnums" (test-union (N)))
               (test-case+ "Test bitwise and of tnums" (test-and (N)))
               (test-case+ "Test arithmetic add of tnums" (test-add (N)))
               (test-case+ "Test shift left by constant" (test-lshift (N)))
               (test-case+ "Test shift right by constant" (test-rshift (N)))
               (test-case+ "Test shift left by tnum" (test-shl (N)))
               (test-case+ "Test shift right by tnum" (test-lshr (N)))
               (test-case+ "Test unknown tnums" (test-unknown (N)))))

(module+ test
  (time (run-tests tnum-tests)))
