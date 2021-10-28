#lang rosette

(provide (all-defined-out))

; log2 that is exact when N is power of two.
(define (log2 N) (exact-floor (log N 2)))

; Whether N is a power of two.
(define (is-pow2? N) (equal? (expt 2 (log2 N)) N))
