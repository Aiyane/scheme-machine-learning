(load "ML.ss")

(define X (vector (vector (NumV  1.31415422e-01) (NumV -2.26093368e-01)) (vector (NumV -5.09640698e-01) (NumV -2.26093368e-01))
                  (vector (NumV  5.07908699e-01) (NumV -2.26093368e-01)) (vector (NumV -7.43677059e-01) (NumV -1.55439190e+00))
                  (vector (NumV  1.27107075e+00) (NumV  1.10220517e+00)) (vector (NumV -1.99450507e-02) (NumV  1.10220517e+00))
                  (vector (NumV -5.93588523e-01) (NumV -2.26093368e-01)) (vector (NumV -7.29685755e-01) (NumV -2.26093368e-01))
                  (vector (NumV -7.89466782e-01) (NumV -2.26093368e-01)) (vector (NumV -6.44465993e-01) (NumV -2.26093368e-01))
                  (vector (NumV -7.71822042e-02) (NumV  1.10220517e+00)) (vector (NumV -8.65999486e-04) (NumV -2.26093368e-01))
                  (vector (NumV -1.40779041e-01) (NumV -2.26093368e-01)) (vector (NumV  3.15099326e+00) (NumV  2.43050370e+00))
                  (vector (NumV -9.31923697e-01) (NumV -2.26093368e-01)) (vector (NumV  3.80715024e-01) (NumV  1.10220517e+00))
                  (vector (NumV -8.65782986e-01) (NumV -1.55439190e+00)) (vector (NumV -9.72625673e-01) (NumV -2.26093368e-01))
                  (vector (NumV  7.73743478e-01) (NumV  1.10220517e+00)) (vector (NumV  1.31050078e+00) (NumV  1.10220517e+00))
                  (vector (NumV -2.97227261e-01) (NumV -2.26093368e-01)) (vector (NumV -1.43322915e-01) (NumV -1.55439190e+00))
                  (vector (NumV -5.04552951e-01) (NumV -2.26093368e-01)) (vector (NumV -4.91995958e-02) (NumV  1.10220517e+00))
                  (vector (NumV  2.40309445e+00) (NumV -2.26093368e-01)) (vector (NumV -1.14560907e+00) (NumV -2.26093368e-01))
                  (vector (NumV -6.90255715e-01) (NumV -2.26093368e-01)) (vector (NumV  6.68172729e-01) (NumV -2.26093368e-01))
                  (vector (NumV  2.53521350e-01) (NumV -2.26093368e-01)) (vector (NumV  8.09357707e-01) (NumV -2.26093368e-01))
                  (vector (NumV -2.05647815e-01) (NumV -1.55439190e+00)) (vector (NumV -1.27280274e+00) (NumV -2.88269044e+00))
                  (vector (NumV  5.00114703e-02) (NumV  1.10220517e+00)) (vector (NumV  1.44532608e+00) (NumV -2.26093368e-01))
                  (vector (NumV -2.41262044e-01) (NumV  1.10220517e+00)) (vector (NumV -7.16966387e-01) (NumV -2.26093368e-01))
                  (vector (NumV -9.68809863e-01) (NumV -2.26093368e-01)) (vector (NumV  1.67029651e-01) (NumV  1.10220517e+00))
                  (vector (NumV  2.81647389e+00) (NumV  1.10220517e+00)) (vector (NumV  2.05187753e-01) (NumV  1.10220517e+00))
                  (vector (NumV -4.28236746e-01) (NumV -1.55439190e+00)) (vector (NumV  3.01854946e-01) (NumV -2.26093368e-01))
                  (vector (NumV  7.20322135e-01) (NumV  1.10220517e+00)) (vector (NumV -1.01841540e+00) (NumV -2.26093368e-01))
                  (vector (NumV -1.46104938e+00) (NumV -1.55439190e+00)) (vector (NumV -1.89112638e-01) (NumV  1.10220517e+00))
                  (vector (NumV -1.01459959e+00) (NumV -2.26093368e-01))))

(define y (vector (NumV -399900) (NumV -329900) (NumV -369000) (NumV -232000) (NumV -539900)
                  (NumV -299900) (NumV -314900) (NumV -198999) (NumV -212000) (NumV -242500)
                  (NumV -239999) (NumV -347000) (NumV -329999) (NumV -699900) (NumV -259900)
                  (NumV -449900) (NumV -299900) (NumV -199900) (NumV -499998) (NumV -599000)
                  (NumV -252900) (NumV -255000) (NumV -242900) (NumV -259900) (NumV -573900)
                  (NumV -249900) (NumV -464500) (NumV -469000) (NumV -475000) (NumV -299900)
                  (NumV -349900) (NumV -169900) (NumV -314900) (NumV -579900) (NumV -285900)
                  (NumV -249900) (NumV -229900) (NumV -345000) (NumV -549000) (NumV -287000)
                  (NumV -368500) (NumV -329900) (NumV -314000) (NumV -299000) (NumV -179900)
                  (NumV -299900) (NumV -239500)))

(define theta `(,(NumV 0.0) ,(NumV 0.0) ,(NumV 0.0)))
(define rate (NumV -0.01))
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
            (let ([a (NumV (/ 1.0 (* 2 m)))])
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
(#(NumV 334302.06398245395)
 #(NumV 99411.44941267566)
 #(NumV 3267.0129025235187))
|#
