#lang rosette

(require "../lib/common.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/unittest)

(define (test-fls)
  (bug-assert (equal? (fls (bv 0 64)) (bv 0 64)))
  (bug-assert (equal? (fls (bv #b101 64)) (bv 3 64)))
  (bug-assert (equal? (fls (bv -1 64)) (bv 64 64)))
  (bug-assert (equal? (fls (bv #b11 64)) (bv 2 64)))

  (define-symbolic* c (bitvector 64))
  (bug-assert (bvule (fls c) c)))

(define test-fls-suite (test-suite+ "Tests for fls" (test-case+ "Tests for fls" (test-fls))))

(module+ test
  (time (run-tests test-fls-suite)))
