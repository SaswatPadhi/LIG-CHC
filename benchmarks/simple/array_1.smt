(set-logic HORN)

; Z3 fails to reject the following incorrect invariant -- returns unknown
;
;(define-fun inv ((a (Array Int Int)) (i Int)) Bool
;  (forall ((j Int)) (=> (and (<= 0 j) (< j i)) (= (select a j) 1))))

(define-fun inv ((a (Array Int Int)) (i Int)) Bool
  (forall ((j Int)) (=> (and (<= 0 j) (< j i)) (= (select a j) j))))

(assert (forall ((a (Array Int Int)) (i Int)) (=> (= i 0) (inv a i))))

(assert (forall ((a (Array Int Int)) (i Int) (a1 (Array Int Int)) (i1 Int))
                (let ((a!1 (and (inv a i) (= a1 (store a i i)) (= i1 (+ i 1)))))
                     (=> a!1 (inv a1 i1)))))

(assert (forall ((a (Array Int Int)) (i Int) (i1 Int))
                (=> (and (inv a i) (<= 0 i1) (< i1 i) (< (select a i1) 0)) false)))

(check-sat)
