#lang rosette

(require serval/lib/debug)

(provide (all-defined-out))

; From kernel documentation: https://www.kernel.org/doc/htmldocs/kernel-api/API-fls64.html
;   fls64 - find last set bit in a 64-bit word
(define (fls val)
  (define N (bitvector-size (type-of val)))
  (define (loop n)
    (cond
      [(equal? n 0) (bug #:msg "fls")]
      [(! (bvzero? (bit (sub1 n) val))) (bv n N)]
      [else (loop (sub1 n))]))
  (if (bvzero? val) (bv 0 N) (loop N)))

(define fls64 fls)
