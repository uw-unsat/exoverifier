#lang rosette

(require "../lib/tnum.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/solver
         serval/lib/unittest)

(define N (make-parameter (let ([s (getenv "BITWIDTH")]) (if s (string->number s) 64))))

(define (test-unknown n)
  (define unknown (tnum-unknown n))

  (define-symbolic* c (bitvector n))

  (bug-assert (tnum-valid? unknown) #:msg "Unknown tnum must be valid")
  (bug-assert (tnum-contains? unknown c) #:msg "Unknown should contain all tnums"))

(define (test-range n)
  (define-symbolic* min max (bitvector n))
  (define c (tnum-range min max))
  (bug-assert (tnum-valid? c) #:msg "tnum range must be valid")

  (define-symbolic* v (bitvector n))
  (bug-assert (=> (&& (bvule min v) (bvule v max)) (tnum-contains? c v))))

(define (test-const n)
  (define-symbolic* c c2 (bitvector n))
  (define const (tnum-const c))

  (bug-assert (tnum-valid? const) #:msg "tnum-const must return valid tnum")
  (bug-assert (<=> (tnum-contains? const c2) (equal? c c2))
              #:msg "tnum-const contains only the constant"))

(define (test-in n)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define-symbolic* v (bitvector n))
  (bug-assert (=> (&& (tnum-in b a) (tnum-contains? a v)) (tnum-contains? b v))))

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

(define (verify-shift-operator n tnum-op bv-op)
  (define a (fresh-tnum n))
  (define b (fresh-tnum n))
  (define c (tnum-op a b))
  (bug-assert (tnum-valid? c) #:msg "result of tnum op must be valid")

  (define-symbolic* x y (bitvector n))
  ; Assume shift amount is valid
  (assume (bvult y (bv n n)))
  (bug-assert (=> (&& (tnum-contains? a x) (tnum-contains? b y)) (tnum-contains? c (bv-op x y)))))

(define (verify-constant-shift-operator n tnum-op bv-op)
  (define a (fresh-tnum n))
  (define-symbolic* shift (bitvector n))
  (define b (tnum-op a shift))
  (bug-assert (tnum-valid? b) #:msg "result of tnum op must be valid")

  (define-symbolic* x (bitvector n))
  (bug-assert (=> (tnum-contains? a x) (tnum-contains? b (bv-op x shift)))))

; Test that tnum->symbolic does the right thing.
(define (test-tnum->symbolic n)
  (define a (fresh-tnum n))
  (define-values (symbolic-a _) (tnum->symbolic a))

  (define-symbolic* c (bitvector n))

  (assume (tnum-contains? a c))
  (check-sat? (solve (assert (equal? symbolic-a c)))))

(define (test-cast)
  (define a (fresh-tnum 64))

  (define b (tnum-cast a (bv 4 64)))
  (bug-assert (tnum-valid? b))

  (define-symbolic* c (bitvector 64))
  (bug-assert (=> (tnum-contains? a c) (tnum-contains? b (concat (bv 0 32) (extract 31 0 c))))))

(define (test-is-const n)
  (define a (fresh-tnum n))
  (define-symbolic* x y (bitvector n))
  (bug-assert (=> (&& (tnum-is-const? a) (tnum-contains? a x) (tnum-contains? a y)) (equal? x y))))

(define (test-clear-subreg)
  (define a (fresh-tnum 64))
  (define-symbolic* x (bitvector 64))
  (define b (tnum-clear-subreg a))
  (bug-assert (tnum-valid? b))
  (bug-assert (=> (tnum-contains? a x) (tnum-contains? b (concat (extract 63 32 x) (bv 0 32))))))

(define (test-subreg-is-const)
  (define a (fresh-tnum 64))
  (define-symbolic* x y (bitvector 64))
  (bug-assert (=> (&& (tnum-is-const? a) (tnum-contains? a x) (tnum-contains? a y))
                  (equal? (extract 31 0 x) (extract 31 0 y)))))

(define (test-const-subreg)
  (define a (fresh-tnum 64))
  (define-symbolic* x y (bitvector 64))
  (define-symbolic* imm (bitvector 32))
  (define b (tnum-const-subreg a imm))
  (bug-assert (tnum-valid? b))
  (bug-assert (=> (tnum-contains? a x) (tnum-contains? b (concat (extract 63 32 x) imm))))
  (bug-assert (=> (tnum-contains? b x) (equal? (extract 31 0 x) imm))))

(define (test-is-unknown n)
  (define a (fresh-tnum n))
  (define-symbolic* x (bitvector n))
  (bug-assert (=> (tnum-is-unknown? a) (tnum-contains? a x))))

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
  (check-unsat? (synthesize #:forall (list as bs)
                            #:guarantee (assert (! (equal? approx-result precise-result))))))

(define tnum-tests
  (test-suite+
   "Tests for tnum"
   (test-case+ "Test tnum->symbolic" (test-tnum->symbolic (N)))
   (test-case+ "Test constant tnums" (test-const (N)))
   (test-case+ "Test tnum range" (test-range (N)))
   (test-case+ "Test tnum is-const" (test-is-const (N)))
   (test-case+ "Test tnum subreg-is-const" (test-subreg-is-const))
   (test-case+ "Test tnum clear-subreg" (test-subreg-is-const))
   (test-case+ "Test tnum const-subreg" (test-const-subreg))
   (test-case+ "Test tnum is-unknown" (test-is-unknown (N)))
   (test-case+ "Test tnum in (subset)" (test-in (N)))
   (test-case+ "Test intersection of tnums" (test-intersect (N)))
   (test-case+ "Test union of tnums" (test-union (N)))
   (test-case+ "Test cast tnum" (test-cast))
   (test-case+ "Test bitwise and of tnums" (verify-binary-operator (N) tnum-and bvand))
   (test-case+ "Test bitwise or of tnums" (verify-binary-operator (N) tnum-or bvor))
   (test-case+ "Test bitwise xor of tnums" (verify-binary-operator (N) tnum-xor bvxor))
   (test-case+ "Test arithmetic add of tnums" (verify-binary-operator (N) tnum-add bvadd))
   (test-case+ "Test arithmetic sub of tnums" (verify-binary-operator (N) tnum-sub bvsub))
   (test-case+ "Test arithmetic mul of tnums" (verify-binary-operator 8 tnum-mul bvmul))
   (test-case+ "Test shift left by constant" (verify-constant-shift-operator (N) tnum-lshift bvshl))
   (test-case+ "Test shift right by constant"
               (verify-constant-shift-operator (N) tnum-rshift bvlshr))
   (test-case+ "Test arithmetic shift right by constant"
               (verify-constant-shift-operator (N) (lambda (a c) (tnum-arshift a c (N))) bvashr))
   (test-case+ "Test shift left by tnum"
               (verify-shift-operator (N) (lambda (a b) (tnum-shl a b (N))) bvshl))
   (test-case+ "Test logical shift right by tnum"
               (verify-shift-operator (N) (lambda (a b) (tnum-lshr a b (N))) bvlshr))
   (test-case+ "Test arithmetic shift right by tnum"
               (verify-shift-operator (N) (lambda (a b) (tnum-ashr a b (N))) bvashr))
   (test-case+ "Test precision of add" (with-z3 (verify-binary-op-precision (N) tnum-add bvadd)))
   ; (test-case+ "Test precision of and" (with-z3 (verify-binary-op-precision (N) tnum-and bvand)))
   (test-case+ "Test precision of or" (with-z3 (verify-binary-op-precision (N) tnum-or bvor)))
   (test-case+ "Test precision of xor" (with-z3 (verify-binary-op-precision (N) tnum-xor bvxor)))
   (test-case+ "Test unknown tnums" (test-unknown (N)))))

(module+ test
  (time (with-prefer-boolector (run-tests tnum-tests))))
