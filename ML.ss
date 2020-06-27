(define-syntax pmatch
  (syntax-rules (else guard)
    [(_ (rator rand ...) cs ...)
      (let ([v (rator rand ...)])
        (pmatch v cs ...))]
    [(_ v) (errorf 'pmatch "failed: ~s" v)]
    [(_ v (else e0 e ...))
      (begin e0 e ...)]
    [(_ v (pat (guard g ...) e0 e ...) cs ...)
      (let ([fk (lambda () (pmatch v cs ...))])
        (ppat v pat 
          (if (and g ...)
              (begin e0 e ...)
              (fk))
          (fk)))]
    [(_ v (pat e0 e ...) cs ...)
      (let ([fk (lambda () (pmatch v cs ...))])
        (ppat v pat (begin e0 e ...) (fk)))]))

(define-syntax ppat
  (syntax-rules (quote unquote)
    [(_ v () kt kf)
      (if (null? v) kt kf)]
    [(_ v (quote lit) kt kf)
      (if (equal? v (quote lit)) kt kf)]
    [(_ v (unquote var) kt kf)
      (let ([var v]) kt)]
    [(_ v (x . y) kt kf)
      (if (pair? v)
          (let ([vx (car v)]
                [vy (cdr v)])
            (ppat vx x (ppat vy y kt kf) kf))
          kf)]
    [(_ v lit kt kf)
      (if (equal? v (quote lit)) kt kf)]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;; delimited control operators ;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(library (reset/shift)
  (export
    reset
    shift)
  (import
    (except (chezscheme) reset))

  (define go #f)
  (define pstack '())

  (define reset*
    (lambda (th)
      (call/cc
        (lambda (k)
          (set! pstack (cons k pstack))
          (go th)))))

  (define shift*
    (lambda (f)
      (call/cc
        (lambda (k)
          (go
            (lambda ()
              (f
                (lambda (v)
                  (call/cc (lambda (k1)
                             (set! pstack (cons k1 pstack))
                             (k v)))))))))))

  (define-syntax reset
    (syntax-rules ()
      [(_ ?e ?f ...)
       (reset* (lambda () ?e ?f ...))]))

  (define-syntax shift
    (syntax-rules ()
      [(_ ?k ?e ?f ...)
       (shift* (lambda (?k) ?e ?f ...))]))

  (define init-delimcc
    (lambda ()
      (let ([v
              (call/cc
                (lambda (k)
                  (set! go k)
                  (k #f)))])
        (if v
            (let* ([r (v)]
                   [h (car pstack)]
                   [_ (set! pstack (cdr pstack))])
              (h r))))))
  (init-delimcc)
)

(import (reset/shift))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;; automatic differentiation ;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
General straight-line example: x is input and x' = ref 0
We denote pᵢⱼ as the jth parameter of ith computation, where pᵢⱼ ∈ {c} ∪ {x} ∪ {yₑ | e < i}
Forward pass:                                                                  Backward pass:
let (y₁, y₁') = (p₁₁ ⊕ p₁₂, ref 0) in ⇓      ⇑ p₁₁' += (d⟦p₁₁ ⊕ p₁₂⟧ / d(p₁₁)) * !y₁';  p₁₂' += (d⟦p₁₁ ⊕ p₁₂⟧ / d(p₁₂)) * !y₁';
let (y₂, y₂') = (p₂₁ ⊕ p₂₂, ref 0) in ⇓      ⇑ p₂₁' += (d⟦p₂₁ ⊕ p₂₂⟧ / d(p₂₁)) * !y₂';  p₂₂' += (d⟦p₂₁ ⊕ p₂₂⟧ / d(p₂₂)) * !y₂';
                                  ... ⇓      ⇑ ...
let (yₓ, yₓ') = (pₓ₁ ⊕ pₓ₂, ref 0) in ⇓      ⇑ pₓ₁' += (d⟦pₓ₁ ⊕ pₓ₂⟧ / d(pₓ₁)) * !yₓ';  pₓ₂' += (d⟦pₓ₁ ⊕ pₓ₂⟧ / d(pₓ₂)) * !yₓ';
                                    yₓ'  :=  1.0;
|#
(define @+ +)
(define @* *)

(define NumV-x cadr)
(define NumF-x cadr)
(define NumF-d caddr)
(define NumF-tag cadddr)
(define NumR-x cadr)
(define NumR-d caddr)
(define NumR-tag cadddr)

(define set-x!
  (lambda (a x)
    (set-cdr! a (cons x (cddr a)))))
(define set-d!
  (lambda (a d)
    (set-cdr! (cdr a) (cons d (cdddr a)))))
(define set-tag!
  (lambda (a tag)
    (set-cdr! (cddr a) (cons tag (cddddr a)))))

(define Zero '(NumV 0.0))
(define One '(NumV 1.0))

(define global-tagger-n -1)
(define (tag-next) (set! global-tagger-n (add1 global-tagger-n)) global-tagger-n)
(define (resetTag) (set! global-tagger-n -1))

(define +
  (lambda (a b)
    (pmatch `(,a ,b)
      [((NumV ,a.x) (NumV ,b.x))
       `(NumV ,(+ a.x b.x))]
      [((NumV ,a.x) (NumF ,b.x ,b.d ,b.tag))
       `(NumF ,(+ a b.x) ,b.d ,b.tag)]
      [((NumV ,a.x) (NumR ,b.x ,b.d ,b.tag))
       (shift k
         (let ([y `(NumR ,(+ a b.x) ,Zero ,b.tag)])
           (k y)
           (set-d! b (+ (NumR-d b) (NumR-d y)))))]
      [((NumF ,a.x ,a.d ,a.tag) (NumV ,b.x))
       `(NumF ,(+ a.x b) ,a.d ,a.tag)]
      [((NumF ,a.x ,a.d ,a.tag) (NumF ,b.x ,b.d ,b.tag))
       (cond
         [(= a.tag b.tag) `(NumF ,(+ a.x b.x) ,(+ a.d b.d) ,a.tag)]
         [(< a.tag b.tag) `(NumF ,(+ a b.x) ,b.d ,b.tag)]
         [else `(NumF ,(+ a.x b) ,a.d ,a.tag)])]
      [((NumR ,a.x ,a.d ,a.tag) (NumV ,b.x))
       (shift k
         (let ([y `(NumR ,(+ a.x b) ,Zero ,a.tag)])
           (k y)
           (set-d! a (+ (NumR-d a) (NumR-d y)))))]
      [((NumR ,a.x ,a.d ,a.tag) (NumR ,b.x ,b.d ,b.tag))
       (shift k
         (let ([y `(NumR ,(+ a.x b.x) ,Zero ,(max a.tag b.tag))])
           (k y)
           (cond
             [(= a.tag b.tag)
              (set-d! a (+ (NumR-d a) (NumR-d y)))
              (set-d! b (+ (NumR-d b) (NumR-d y)))]
             [(< a.tag b.tag) (set-d! b (+ (NumR-d b) (NumR-d y)))]
             [else (set-d! a (+ (NumR-d a) (NumR-d y)))])))]
      [,other (@+ a b)])))

(define *
  (lambda (a b)
    (pmatch `(,a ,b)
      [((NumV ,a.x) (NumV ,b.x))
       `(NumV ,(* a.x b.x))]
      [((NumV ,a.x) (NumF ,b.x ,b.d ,b.tag))
       `(NumF ,(* a b.x) ,(* a b.d) ,b.tag)]
      [((NumV ,a.x) (NumR ,b.x ,b.d ,b.tag))
       (shift k
         (let ([y `(NumR ,(* a b.x) ,Zero ,b.tag)])
           (k y)
           (set-d! b (+ (NumR-d b) (* a (NumR-d y))))))]
      [((NumF ,a.x ,a.d ,a.tag) (NumV ,b.x))
       `(NumF ,(* a.x b) ,(* a.d b) ,a.tag)]
      [((NumF ,a.x ,a.d ,a.tag) (NumF ,b.x ,b.d ,b.tag))
       (cond
         [(= a.tag b.tag) `(NumF ,(* a.x b.x) ,(+ (* a.d b.x) (* a.x b.d)) ,a.tag)]
         [(< a.tag b.tag) `(NumF ,(* a b.x) ,(* a b.d) ,b.tag)]
         [else `(NumF ,(* a.x b) ,(* a.d b) ,a.tag)])]
      [((NumR ,a.x ,a.d ,a.tag) (NumV ,b.x))
       (shift k
         (let ([y `(NumR ,(* a.x b) ,Zero ,a.tag)])
           (k y)
           (set-d! a (+ (NumR-d a) (* b (NumR-d y))))))]
      [((NumR ,a.x ,a.d ,a.tag) (NumR ,b.x ,b.d ,b.tag))
       (shift k
         (let ([y `(NumR ,(* a.x b.x) ,Zero ,(max a.tag b.tag))])
           (k y)
           (cond
             [(= a.tag b.tag)
              (set-d! a (+ (NumR-d a) (* b.x (NumR-d y))))
              (set-d! b (+ (NumR-d b) (* a.x (NumR-d y))))]
             [(< a.tag b.tag) (set-d! b (+ (NumR-d b) (* a.x (NumR-d y))))]
             [else (set-d! a (+ (NumR-d a) (* b.x (NumR-d y))))])))]
      [,other (@* a b)])))

(define grad
  (lambda (f)
    (lambda (x)
      (let ([z `(NumR ,x ,Zero ,(tag-next))])
        (reset (set-d! (f z) One))
        (NumR-d z)))))

(define grad^
  (lambda (f)
    (lambda (x)
      (NumF-d (f `(NumF ,x ,One ,(tag-next)))))))

#|
((grad
   (lambda (x)
     (let ([should-be-one ((grad (lambda (y) (+ x y))) One)])
       (printf "should-be-one is ~a\n" should-be-one)
       (printf "x should not yet have any gradient, but: x = ~a\n" x)
       (* x `(NumR ,should-be-one ,Zero 0)))))
 One) ; 1
(define g (lambda (x) (* x (* x x))))
(define g1 (grad g))
(define g2 (grad^ g1))
(define g3 (grad^ g2))
(g1 '(NumV 4.0)) ; 48
(g2 '(NumV 4.0)) ; 24
(g3 '(NumV 4.0)) ; 6

> (define g (lambda (x) (+ (+ (* '(NumV 3) x) (* x x)) (* '(NumV 4) (+ x '(NumV 5))))))
> (define g1 (grad g))
> (define g2 (grad^ g1))
> (g1 '(NumV 4.0))
(NumV 15.0)
> (g2 '(NumV 4.0))
(NumV 2.0)
|#

(define grad-n
  (lambda (f)
    (lambda (args)
      (let ([res '()])
        (let loop ([before '()]
                   [x (car args)]
                   [after (cdr args)])
          (let* ([z `(NumR ,x ,Zero ,(tag-next))]
                 [args (append before (cons z after))])
            (reset (set-d! (f args) One))
            (set! res (append res `(,(NumR-d z))))
            (if (null? after)
                res
                (loop (append before `(,x)) (car after) (cdr after)))))))))

#|
(define vs '((NumV 2) (NumV 3) (NumV 4)))
(define ms '((NumV 3) (NumV 4) (NumV 5)))

(define g
  (lambda (ms)
    (let loop ([ms (cdr ms)]
               [vs (cdr vs)]
               [e (* (* (car ms) (car ms)) (car vs))])
      (if (null? ms)
          e
          (loop (cdr ms) (cdr vs)
                (+ e (* (* (car ms) (car ms)) (car vs))))))))

(define g1 (grad-n g))
(g1 ms) ; (12 24 40)
|#


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; test ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define X (vector (vector '(NumV  1.31415422e-01) '(NumV -2.26093368e-01)) (vector '(NumV -5.09640698e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV  5.07908699e-01) '(NumV -2.26093368e-01)) (vector '(NumV -7.43677059e-01) '(NumV -1.55439190e+00))
                  (vector '(NumV  1.27107075e+00) '(NumV  1.10220517e+00)) (vector '(NumV -1.99450507e-02) '(NumV  1.10220517e+00))
                  (vector '(NumV -5.93588523e-01) '(NumV -2.26093368e-01)) (vector '(NumV -7.29685755e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV -7.89466782e-01) '(NumV -2.26093368e-01)) (vector '(NumV -6.44465993e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV -7.71822042e-02) '(NumV  1.10220517e+00)) (vector '(NumV -8.65999486e-04) '(NumV -2.26093368e-01))
                  (vector '(NumV -1.40779041e-01) '(NumV -2.26093368e-01)) (vector '(NumV  3.15099326e+00) '(NumV  2.43050370e+00))
                  (vector '(NumV -9.31923697e-01) '(NumV -2.26093368e-01)) (vector '(NumV  3.80715024e-01) '(NumV  1.10220517e+00))
                  (vector '(NumV -8.65782986e-01) '(NumV -1.55439190e+00)) (vector '(NumV -9.72625673e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV  7.73743478e-01) '(NumV  1.10220517e+00)) (vector '(NumV  1.31050078e+00) '(NumV  1.10220517e+00))
                  (vector '(NumV -2.97227261e-01) '(NumV -2.26093368e-01)) (vector '(NumV -1.43322915e-01) '(NumV -1.55439190e+00))
                  (vector '(NumV -5.04552951e-01) '(NumV -2.26093368e-01)) (vector '(NumV -4.91995958e-02) '(NumV  1.10220517e+00))
                  (vector '(NumV  2.40309445e+00) '(NumV -2.26093368e-01)) (vector '(NumV -1.14560907e+00) '(NumV -2.26093368e-01))
                  (vector '(NumV -6.90255715e-01) '(NumV -2.26093368e-01)) (vector '(NumV  6.68172729e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV  2.53521350e-01) '(NumV -2.26093368e-01)) (vector '(NumV  8.09357707e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV -2.05647815e-01) '(NumV -1.55439190e+00)) (vector '(NumV -1.27280274e+00) '(NumV -2.88269044e+00))
                  (vector '(NumV  5.00114703e-02) '(NumV  1.10220517e+00)) (vector '(NumV  1.44532608e+00) '(NumV -2.26093368e-01))
                  (vector '(NumV -2.41262044e-01) '(NumV  1.10220517e+00)) (vector '(NumV -7.16966387e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV -9.68809863e-01) '(NumV -2.26093368e-01)) (vector '(NumV  1.67029651e-01) '(NumV  1.10220517e+00))
                  (vector '(NumV  2.81647389e+00) '(NumV  1.10220517e+00)) (vector '(NumV  2.05187753e-01) '(NumV  1.10220517e+00))
                  (vector '(NumV -4.28236746e-01) '(NumV -1.55439190e+00)) (vector '(NumV  3.01854946e-01) '(NumV -2.26093368e-01))
                  (vector '(NumV  7.20322135e-01) '(NumV  1.10220517e+00)) (vector '(NumV -1.01841540e+00) '(NumV -2.26093368e-01))
                  (vector '(NumV -1.46104938e+00) '(NumV -1.55439190e+00)) (vector '(NumV -1.89112638e-01) '(NumV  1.10220517e+00))
                  (vector '(NumV -1.01459959e+00) '(NumV -2.26093368e-01))))


(define y (vector '(NumV -399900) '(NumV -329900) '(NumV -369000) '(NumV -232000) '(NumV -539900)
                  '(NumV -299900) '(NumV -314900) '(NumV -198999) '(NumV -212000) '(NumV -242500)
                  '(NumV -239999) '(NumV -347000) '(NumV -329999) '(NumV -699900) '(NumV -259900)
                  '(NumV -449900) '(NumV -299900) '(NumV -199900) '(NumV -499998) '(NumV -599000)
                  '(NumV -252900) '(NumV -255000) '(NumV -242900) '(NumV -259900) '(NumV -573900)
                  '(NumV -249900) '(NumV -464500) '(NumV -469000) '(NumV -475000) '(NumV -299900)
                  '(NumV -349900) '(NumV -169900) '(NumV -314900) '(NumV -579900) '(NumV -285900)
                  '(NumV -249900) '(NumV -229900) '(NumV -345000) '(NumV -549000) '(NumV -287000)
                  '(NumV -368500) '(NumV -329900) '(NumV -314000) '(NumV -299000) '(NumV -179900)
                  '(NumV -299900) '(NumV -239500)))


(define theta '((NumV 0.0) (NumV 0.0) (NumV 0.0)))
(define rate '(NumV -0.01))
(define loop-nums 400)

; h = b + w₀x₀ + w₁x₁ + ... + w₇x₇
(define ^
  (lambda (a)
    (* a a)))

(define h
  (lambda (ws xs)
    (let ([len (length ws)])
      (let loop ([i 1] [e (car ws)] [ws (cdr ws)])
        (if (< i len)
            (let ([wi (car ws)]
                  [xi (vector-ref xs (sub1 i))])
              (loop (add1 i) (+ e (* wi xi)) (cdr ws)))
            e)))))

; J = 1/2m * (((h x₀) - y₀)^2 + ((h x₁) - y₁)^2 + ... + ((h x₉) - y₉)^2)
(define sub-loss
  (lambda (ws xs yi)
    (^ (+ (h ws xs) yi))))

(define J
  (lambda (ws)
    (let ([m (vector-length X)]
          [xs0 (vector-ref X 0)]
          [y0 (vector-ref y 0)])
      (let loop ([i 1] [e (sub-loss ws xs0 y0)])
        (if (< i m)
            (let ([xs (vector-ref X i)]
                  [yi (vector-ref y i)])
              (loop (add1 i) (+ e (sub-loss ws xs yi))))
            (let ([a `(NumV ,(/ 1.0 (* 2 m)))])
              (* a e)))))))

(define linear-regression
  (lambda ()
    (let ([len (length theta)])
      (let loop ([theta theta] [n 0])
        (if (< n loop-nums)
            (let sub-loop ([theta theta]
                           [dJs ((grad-n J) theta)]
                           [next-theta '()])
              (if (null? theta)
                  (loop next-theta (add1 n))
                  (let* ([thetai (car theta)]
                         [dJi (car dJs)]
                         [item (+ thetai (* rate dJi))])
                    (sub-loop (cdr theta) (cdr dJs)
                              (append next-theta `(,item))))))
            theta)))))

#|
> (linear-regression)
((NumV 334302.06398245395)
 (NumV 99411.44941267566)
 (NumV 3267.0129025235187))

comparative results: results in python
[[334302.06399328]
[ 99411.44947359]
[  3267.01285407]]
|#
