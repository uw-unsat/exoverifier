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

(define S64_MIN (bvshl (bv 1 64) (bv 63 64)))
(define S64_MAX (bvnot S64_MIN))
(define U64_MAX (bv -1 64))
(define S32_MIN (bvshl (bv 1 32) (bv 31 32)))
(define S32_MAX (bvnot S32_MIN))
(define U32_MAX (bv -1 32))
