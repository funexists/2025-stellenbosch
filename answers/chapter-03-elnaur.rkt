#lang pie

(claim at-least-two?
  (-> Nat
      Atom
      ))

(define at-least-two?
  (lambda (n)
    (which-Nat n
      'nil
      (lambda (n1)
        (which-Nat n1
          'nil
          (lambda (n2)
            't))))))
