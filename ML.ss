(load "base-language.ss")

(define @+ +)
(define @* *)

(struct NumV (x))
(struct NumF (x d tag))
(struct NumR (x d tag))

(define Zero (NumV 0.0))
(define One (NumV 1.0))

(define id
  (let ([a -1])
    (λ ()
      (set! a (+ a 1))
      a)))

(define +
  (case-λ
    [((NumV a (x)) (NumV b (x2)))
     (NumV (+ x x2))]
    [((NumV a (v)) (NumF b (x d tag)))
     (NumF (+ a x) d tag)]
    [((NumF a (x d tag)) (NumV b (v)))
     (NumF (+ x b) d tag)]
    [((NumV a (v)) (NumR b (x d tag)))
       (shift k
         (let ([y (NumR (+ a x) Zero tag)])
           (k y)
           (set-NumR-d! b (+ (NumR:d b) (NumR:d y)))))]
    [((NumR a (x d tag)) (NumV b (v)))
       (shift k
         (let ([y (NumR (+ x b) Zero tag)])
           (k y)
           (set-NumR-d! a (+ (NumR:d a) (NumR:d y)))))]
    [((NumF a (x d tag)) (NumF b (x2 d2 tag2)))
     (cond
       [(= tag tag2) (NumF (+ x x2) (+ d d2) tag)]
       [(< tag tag2) (NumF (+ a x2) d2 tag2)]
       [else (NumF (+ x b) d tag)])]
    [((NumR a (x d tag)) (NumR b (x2 d2 tag2)))
     (shift k
       (let ([y (NumR (+ x x2) Zero (max tag tag2))])
         (k y)
         (cond
           [(= tag tag2)
            (set-NumR-d! a (+ (NumR:d a) (NumR:d y)))
            (set-NumR-d! b (+ (NumR:d b) (NumR:d y)))]
           [(< tag tag2)
            (set-NumR-d! b (+ (NumR:d b) (NumR:d y)))]
           [else
            (set-NumR-d! a (+ (NumR:d a) (NumR:d y)))])))]
    [(a b)
     (@+ a b)]))

(define *
  (case-λ
    [((NumV a (x)) (NumV b (x2)))
     (NumV (* x x2))]
    [((NumV a (v)) (NumF b (x d tag)))
     (NumF (* a x) (* a d) tag)]
    [((NumF a (x d tag)) (NumV b (v)))
     (NumF (* x b) (* d b) tag)]
    [((NumV a (v)) (NumR b (x d tag)))
       (shift k
         (let ([y (NumR (* a x) Zero tag)])
           (k y)
           (set-NumR-d! b (+ (NumR:d b) (* a (NumR:d y))))))]
    [((NumR a (x d tag)) (NumV b (v)))
       (shift k
         (let ([y (NumR (* x b) Zero tag)])
           (k y)
           (set-NumR-d! a (+ (NumR:d a) (* b (NumR:d y))))))]
    [((NumF a (x d tag)) (NumF b (x2 d2 tag2)))
     (cond
       [(= tag tag2) (NumF (* x x2) (+ (* d x2) (* x d2)) tag)]
       [(< tag tag2) (NumF (* a x2) (* a d2) tag2)]
       [else (NumF (* x b) (* d b) tag)])]
    [((NumR a (x d tag)) (NumR b (x2 d2 tag2)))
     (shift k
       (let ([y (NumR (* x x2) Zero (max tag tag2))])
         (k y)
         (cond
           [(= tag tag2)
            (set-NumR-d! a (+ (NumR:d a) (* x2 (NumR:d y))))
            (set-NumR-d! b (+ (NumR:d b) (* x (NumR:d y))))]
           [(< tag tag2)
            (set-NumR-d! b (+ (NumR:d b) (* x (NumR:d y))))]
           [else
            (set-NumR-d! a (+ (NumR:d a) (* x2 (NumR:d y))))])))]
    [(a b)
     (@* a b)]))

(define grad
  (λ (f)
    (λ (x)
      (let ([z (NumR x Zero (id))])
        (reset (set-NumR-d! (f z) One))
        (NumR:d z)))))

(define grad^
  (λ (f)
    (λ (x)
      (NumF:d (f (NumF x One (id)))))))

(define grad-n
  (λ (f)
    (λ (args)
      (let ([res '()])
        (let loop ([before '()]
                   [x (car args)]
                   [after (cdr args)])
          (let* ([z (NumR x Zero (id))]
                 [args (append before (cons z after))])
            (reset (set-NumR-d! (f args) One))
            (set! res (append res `(,(NumR:d z))))
            (if (null? after)
                res
                (loop (append before `(,x)) (car after) (cdr after)))))))))

#|
> (define vs `(,(NumV 2) ,(NumV 3) ,(NumV 4)))
> (define ms `(,(NumV 3) ,(NumV 4) ,(NumV 5)))
> (define g
      (λ (ms)
        (let loop ([ms (cdr ms)]
                   [vs (cdr vs)]
                   [e (* (* (car ms) (car ms)) (car vs))])
          (if (null? ms)
              e
              (loop (cdr ms) (cdr vs)
                    (+ e (* (* (car ms) (car ms)) (car vs))))))))
> (define g1 (grad-n g))
> (g1 ms)
(#(NumV 12.0) #(NumV 24.0) #(NumV 40.0))
|#
