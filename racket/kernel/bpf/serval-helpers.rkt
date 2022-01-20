#lang rosette

(provide (all-defined-out))

(define (@serval_fresh_u64)
  (define-symbolic* fresh_u64 (bitvector 64))
  fresh_u64)
