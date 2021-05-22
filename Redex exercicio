#lang racket
;A redex tutorial exercises

(require redex)
(require redex/tut-subst)

(define-language L
  (e (e e)
     (λ (x t) e)
     x
     (amb t e ...)
     number
     (+ e ...)
     (if0 e e e)
     (fix e))
  (t (→ t t)
     num)
  (x variable-not-otherwise-mentioned))

(display "Exercise 1:\n")
(redex-match L
             ((_ (_ _) e_1) _)
             (term ((λ (x num) (+ x 1))17)))

;return: (list (match (list (bind 'e_1 '(+ x 1)))))



(display "Exercise 2:\n")
(redex-match L
             (→ num t_1)
             (term (→ num (→ num num))))

;return: (list (match (list (bind 't_1 'num))))



;;_ ... -> list

(display "Exercise 3:\n")

(redex-match L
             (_ ... e_1 e_2 _ ...)
             (term (1 2 3 4)))
;return: (list
;         (match (list (bind 'e_1 1) (bind 'e_2 2)))
;         (match (list (bind 'e_1 2) (bind 'e_2 3)))
;         (match (list (bind 'e_1 3) (bind 'e_2 4))))



;;_ ..._1 _ ..._1 -> lists with the same number of terms

(display "Exercise 4: \n")

(redex-match L
             (_ ..._1 e_left _ ..._2 _ _ ..._2 e_right _ ..._1)
             (term(1 2 3 4 5)))

;return: (list
;         (match (list (bind 'e_left 1) (bind 'e_right 5)))
;         (match (list (bind 'e_left 2) (bind 'e_right 4))))

(define-extended-language L+Γ L
  [Γ · (x : t Γ)])
;lista encadeada onde vc tem o tipo e o contexto e o ponteiro pro proximo contexto seria gama ali, mas se fosse um ponto, seria null
;→ representa funçao

(define-judgment-form
  L+Γ
  #:mode (types I I O) ;input input output
  #:contract (types Γ e t) ;'gama' and 'e' == input // 't' == output

  [(types Γ e_1 (→ t_2 t_3)) ;if e_1 has this type (→ t_2 t_3)
   (types Γ e_2 t_2) ;and e_2 has this type t_2
   -------------------------
   (types Γ (e_1 e_2) t_3)] ;then the application expression (e_1 e_2) has the type t_3
 
  [(types (x : t_1 Γ) e t_2)
   ;λ ---> (→ t_1 t_2)
   -----------------------------------
   (types Γ (λ (x t_1) e) (→ t_1 t_2))]
 
  [(types Γ e (→ (→ t_1 t_2) (→ t_1 t_2)))
   ;fix -----> (→ t_1 t_2)
   ---------------------------------------
   (types Γ (fix e) (→ t_1 t_2))]
 
  [---------------------
   (types (x : t Γ) x t)] ;x has the type t, the expression is x, so the x type is t
                          ;mas ela precisa ter tipo t no inicio
  [(types Γ x_1 t_1)
   ;(side-condition (different x_1 x_2)) ;caso nao seja ele define o tipo pois eu posso ter x, y, z. mas se forem iguais vc ja achou o tipo e nao precisa ser redefinido, ai a regra nao se aplica.
   ------------------------------------
   (types (x_2 : t_2 Γ) x_1 t_1)]
 
  [(types Γ e num) ...
   ;+ vai ter o mesmo tipo que o num se o 'e' for num
   -----------------------
   (types Γ (+ e ...) num)]
 
  [--------------------
   ;todo num é um number
   (types Γ number num)]
 
  [(types Γ e_1 num)
   (types Γ e_2 t)
   (types Γ e_3 t)
   ;se -> e_1 for do mesmo tipo que o num
   ;   -> e_2 for do mesmo tipo que o t
   ;   -> e_3 for do mesmo tipo que o t
   ;entao if0 tera o mesmo tipo que o t
   -----------------------------
   (types Γ (if0 e_1 e_2 e_3) t)]

 #| [(types Γ e num) ...
   --------------------------
   (types Γ (amb e ...) num)]
 |#
  [(types Γ e t_2) ...
   ; need a side condition
   (side-condition (allEquals t_1 t_2 ...))
   ------------------------------
   (types Γ (amb t_1 e ...) t_1)])


(define-metafunction L+Γ
  [(different x_1 x_1) #f]
  [(different x_1 x_2) #t])

(define-metafunction L+Γ
  allEquals : t ... -> boolean
  [(allEquals) #t]
  [(allEquals t) #t]
  [(allEquals t t t_1 ...) (allEquals t t_1 ...)]
  [(allEquals t _ ...) #f])



(display "Exercise 5:\n")
(judgment-holds
   (types ·
          (λ (y (→ num num)) (λ (y num) y)) t) t)
#|
 Sem o comentario do side condition retorna: '((→ (→ num num) (→ num num)))

 Com o comentario retorna: '((→ (→ num num) (→ num (→ num num)))
                            (→ (→ num num) (→ num num)))

pq sem a side condition o programa vai pegar todos os types 
|#

(display "Exercise 6:\n")

(judgment-holds
   (types ·
          (λ (f (→ num (→ num num))) (f (amb num 1 8)))
          (→ t_1 t_2))
   t_2)

;reducing

(define-extended-language Ev L+Γ
  (p (e ...))
  (P (e ... E e ...))
  (E (v E)
     (E e)
     (+ v ... E e ...)
     (if0 E e e)
     (fix E)
     hole)
  (v (λ (x t) e)
     (fix v)
     number))

(define-metafunction Ev
  Σ : number ... -> number
  [(Σ number ...)
   ,(apply + (term (number ...)))])


(define-metafunction Ev
  subst : x v e -> e
  [(subst x v e)
   ,(subst/proc x? (list (term x)) (list (term v)) (term e))])
(define x? (redex-match Ev x))


(define red
  (reduction-relation
   Ev
   #:domain p
   (--> (in-hole P (if0 0 e_1 e_2)) ;retorna o primeiro a direita do 0?
        (in-hole P e_1)
        "if0t")
   (--> (in-hole P (if0 v e_1 e_2)) 
        (in-hole P e_2)
        (side-condition (not (equal? 0 (term v)))) 
        "if0f")
   (--> (in-hole P ((fix (λ (x t) e)) v))
        (in-hole P (((λ (x t) e) (fix (λ (x t) e))) v)) ;recursao?
        "fix")
   (--> (in-hole P ((λ (x t) e) v))
        (in-hole P (subst x v e))
        "βv")
   (--> (in-hole P (+ number ...))
        (in-hole P (Σ number ...))
        "+")
   (--> (e_1 ... (in-hole E (amb e_2 ...)) e_3 ...) ;amb é listas?
        (e_1 ... (in-hole E e_2) ... e_3 ...)
        "amb")))
(display "Tests:\n")


(traces red
        (term ((+ (amb 1 2)
                  (amb 10 20))))) ;pq nao funciona?

(traces red
          (term ((if0 0 2 3)))) ;pq so reduz com 2 parenteses "((if0 0 2 3))"?

(traces red
          (term ((fix (λ (x num) (+ 1 2)) 2)))) ; como usa esse fix

(traces red
        (term ((+ (+ 1 2) (if0 5 8 9)))))

(traces red
          (term ((if0 0 (if0 1 0 (if0 0 2 (if0 1 2 3))) 1))))

(traces red
        (term ((+ (+ 1 2) (if0 0 8 9)))))

(traces red
        (term ((+ (+ 1 2) (if0 5 8 x)))))

(display "Exercise 8:\n")
(define (reduce n)
  (traces red
          (term ((fix (+ n -1)))))) ;usar o lambda?
