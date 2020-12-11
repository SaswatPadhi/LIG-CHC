(set-logic HORN)

(define-fun inv ((x_0 (Array Int Int)) (x_1 Int)) Bool
  (forall ((j Int)) (=> (and (<= 0 j) (< j x_1)) (= (select x_0 j) 1))))

(assert (forall ((a (Array Int Int))) (=> true (inv a 0))))

(assert (forall ((a (Array Int Int)) (i Int) (a1 (Array Int Int)) (i1 Int))
                (let ((a!1 (and (inv a i) (= a1 (store a i 1)) (= i1 (+ i 1)))))
                     (=> a!1 (inv a1 i1)))))

(assert (forall ((a (Array Int Int)) (i Int) (i1 Int))
                (=> (and (inv a i) (<= 0 i1) (< i1 i) (< (select a i1) 0)) false)))

(check-sat)
