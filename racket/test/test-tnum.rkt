#lang rosette

(require "../lib/tnum.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/solver
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

(define (verify-binary-operator n tnum-op bv-op)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-op a b))
  (bug-assert (tnum-valid? c) #:msg "result of tnum op must be valid")

  (define-symbolic* x y (bitvector n))
  (bug-assert (=> (&& (tnum-contains? a x) (tnum-contains? b y)) (tnum-contains? c (bv-op x y)))))

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

(define (verify-binary-op-precision n tnum-op bv-op)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-op a b))

  (define-values (approx-result _) (tnum->symbolic c))

  (define-values (symbolic-a as) (tnum->symbolic a))
  (define-values (symbolic-b bs) (tnum->symbolic b))

  (define precise-result (bv-op symbolic-a symbolic-b))

  ; Search for input tnums a and b and approximate result, such that, for any interpretation
  ; of the precise result, the precise result and the approximate result are unequal.
  ; If no solution exists, then every value represented by approximate result is in the precise
  ; result, so the approximate result is as precise as can be.
  (check-unsat?
    (synthesize #:forall (list as bs)
                #:guarantee (assert (! (equal? approx-result precise-result))))))

(define tnum-tests
  (test-suite+ "Tests for tnum"
               (test-case+ "Test constant tnums" (test-const (N)))
               (test-case+ "Test intersection of tnums" (test-intersect (N)))
               (test-case+ "Test union of tnums" (test-union (N)))
               (test-case+ "Test bitwise and of tnums" (verify-binary-operator (N) tnum-and bvand))
               (test-case+ "Test arithmetic add of tnums" (verify-binary-operator (N) tnum-add bvadd))
               (test-case+ "Test shift left by constant" (test-lshift (N)))
               (test-case+ "Test shift right by constant" (test-rshift (N)))
               (test-case+ "Test shift left by tnum" (test-shl (N)))
               (test-case+ "Test shift right by tnum" (test-lshr (N)))
               (test-case+ "Test precision of add" (with-z3 (verify-binary-op-precision (N) tnum-add bvadd)))
               (test-case+ "Test precision of and" (with-z3 (verify-binary-op-precision (N) tnum-and bvand)))
               (test-case+ "Test unknown tnums" (test-unknown (N)))))

(module+ test
  (time (with-prefer-boolector (run-tests tnum-tests))))
