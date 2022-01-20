#lang rosette

(require serval/lib/core
         serval/lib/unittest
         (prefix-in tnum: "../../lib/tnum.rkt")
         (prefix-in llvm: serval/llvm)
         "../../kernel/bpf/main.rkt")

(define (run-basic-test)
  (parameterize ([llvm:current-machine (llvm:make-machine null null)])
    (define-symbolic* x y u v (bitvector 64))

    (define a (tnum:tnum x y))
    (define b (tnum:tnum u v))
    (define c (tnum:tnum-add a b))

    (define d (apply tnum:tnum (@tnum_add x y u v)))

    (bug-assert (equal? c d) #:msg "test tnum_add")))

(define (test-driver)
  (parameterize ([llvm:current-machine (llvm:make-machine null null)])
    (define result (@driver_main))
    (bug-assert (bvzero? result))))

(define tnum-tests
  (test-suite+ "Kernel tnum tests"
               (test-case+ "simple tests" (run-basic-test))
               (test-case+ "test driver" (test-driver))))

(module+ test
  (time (with-prefer-boolector (run-tests tnum-tests))))
