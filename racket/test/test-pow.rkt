#lang rosette

(require "../lib/pow.rkt"
         rosette/lib/roseunit
         serval/lib/debug
         serval/lib/unittest)

(define (test-pow2)
  (bug-assert (is-pow2? 8))
  (bug-assert (is-pow2? 64))

  (bug-assert (! (is-pow2? 7)))
  (bug-assert (! (is-pow2? 9)))

  (bug-assert (equal? (log2 8) 3))
  (bug-assert (equal? (log2 32) 5))
  (bug-assert (equal? (log2 64) 6)))

(define test-pow2-suite (test-suite+ "Tests for pow2" (test-case+ "Tests for pow2" (test-pow2))))

(module+ test
  (time (run-tests test-pow2-suite)))
