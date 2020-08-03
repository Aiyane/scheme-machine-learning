(define-syntax λ
  (syntax-rules ()
    [(_ arg* bd bd* ...)
     (lambda arg* bd bd* ...)]))

(define-syntax struct
  (letrec ([build-name
             (λ (tem . args)
               (datum->syntax tem
                 (string->symbol
                   (apply string-append
                     (map (λ (x)
                            (if (string? x)
                                x
                                (symbol->string (syntax->datum x))))
                       args)))))])
    (λ (x)
      (syntax-case x ()
        [(_ name (field ...))
         (and (identifier? #'name)
              (andmap identifier? #'(field ...)))
         (with-syntax
           ([maker (build-name #'name #'name)]
            [pred (build-name #'name #'name "?")]
            [(acc ...)
             (map (λ (f) (build-name f #'name ":" f))
               #'(field ...))]
            [(mut ...)
             (map (λ (f) (build-name f "set-" #'name "-" f "!"))
               #'(field ...))]
            [len (add1 (length (syntax->list #'(field ...))))]
            [(index ...)
             (let loop ([n 1] [ls #'(field ...)])
               (if (null? ls)
                   '()
                   (cons n (loop (add1 n) (cdr ls)))))])
           #'(begin
              (define maker
                (λ (field ...)
                  (vector 'name field ...)))
              (define pred
                (λ (obj)
                  (and (vector? obj)
                       (= (vector-length obj) len)
                       (eq? (vector-ref obj 0) 'name))))
              (define acc
                (λ (obj)
                  (if (pred obj)
                      (vector-ref obj index)
                      (errorf 'acc "~s is not a ~s record" obj 'name))))
              ...
              (define mut
                (λ (obj newval)
                  (if (pred obj)
                      (vector-set! obj index newval)
                      (errorf 'mut "~s is not a ~s record" obj 'name))))
              ...))]))))

(define-syntax case-λ
  (let ([build-name
          (λ (tem . args)
            (datum->syntax tem
              (string->symbol
                (apply string-append
                  (map (λ (x)
                         (if (string? x)
                             x
                             (symbol->string (syntax->datum x))))
                    args)))))])
    (λ (x)
      (syntax-case x ()
        [(_ [() exp0 exp1 ...])
         #'(λ ()
            exp0 exp1 ...)]
        [(_ [((Type name (field ...)) args ...) exp0 exp1 ...])
         #'(λ vals
            (_arg-set! [vals (Type name (field ...))] exp0 exp1 ...))]
        [(_ [(arg0 args ...) exp0 exp1 ...])
         #'(λ (arg0 args ...)
            exp0 exp1 ...)]
        [(_ [() exp0 exp1 ...] clause ...)
         #'(λ vals
            (if (null? vals)
                ((case-λ [() exp0 exp1 ...]))
                (apply (case-λ clause ...) vals)))]
        [(_ [((Type name (field ...)) args ...) exp0 exp1 ...] clause ...)
         #'(λ vals
            (if (_pred-type vals (Type name (field ...)) args ...)
                (_arg-set! [vals (Type name (field ...)) args ...] exp0 exp1 ...)
                (apply (case-λ clause ...) vals)))]
        [(_ [(arg0 args ...) exp0 exp1 ...] clause ...)
         (with-syntax
           ([len (add1 (length (syntax->list #'(args ...))))])
            #'(λ vals
               (if (eq? (length vals) len)
                   (apply (case-λ [(arg0 args ...) exp0 exp1 ...]) vals)
                   (apply (case-λ clause ...) vals))))]))))

(define-syntax _arg-set!
  (λ (x)
    (syntax-case x ()
      [(_ [vals (Type name (field ...))] exp0 exp1 ...)
        (with-syntax
          ([(index ...)
            (let loop ([n 1] [ls #'(field ...)])
              (if (null? ls)
                  '()
                  (cons n (loop (add1 n) (cdr ls)))))])
          #'(let ([val (car vals)])
              (let ([name val]
                    [field (vector-ref val index)] ...)
                exp0 exp1 ...)))]
      [(_ [vals (Type name (field ...)) arg0 arg1 ...] exp0 exp1 ...)
        (with-syntax
          ([(index ...)
            (let loop ([n 1] [ls #'(field ...)])
              (if (null? ls)
                  '()
                  (cons n (loop (add1 n) (cdr ls)))))])
          #'(let ([val (car vals)])
              (let ([name val]
                    [field (vector-ref val index)] ...)
                (_arg-set! [(cdr vals) arg0 arg1 ...] exp0 exp1 ...))))])))

(define-syntax _pred-type
  (let ([build-name
          (λ (tem . args)
            (datum->syntax tem
              (string->symbol
                (apply string-append
                  (map (λ (x)
                         (if (string? x)
                             x
                             (symbol->string (syntax->datum x))))
                    args)))))])
    (λ (x)
      (syntax-case x ()
        [(_ vals (Type name (field ...)))
        (with-syntax
          ([pred (build-name #'Type #'Type "?")])
          #'(if (pred (car vals)) #t #f))]
        [(_ vals (Type name (field ...)) arg0 arg* ...)
        (with-syntax
          ([pred (build-name #'Type #'Type "?")])
          #'(if (pred (car vals))
                (_pred-type (cdr vals) arg0 arg* ...)
                #f))]))))

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
