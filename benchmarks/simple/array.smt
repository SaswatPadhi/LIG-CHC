(set-logic HORN)

(define-fun inv ((x_0 (Array Int Int)) (x_1 Int) (x_2 Int)) Bool
  (and (<= x_1 x_2) (forall ((j Int)) (=> (and (<= 0 j) (< j x_1)) (= (select x_0 j) j)))))

(assert (forall ((a (Array Int Int)) (i Int) (val Int) (N Int)) (=> (and (= i 0) (< i N) (= val 7)) (inv a i val N))))

(assert (forall ((a (Array Int Int)) (i Int) (N Int) (a1 (Array Int Int)) (i1 Int))
                (let ((a!1 (and (inv a i N) (< i N) (= a1 (store a i i)) (= i1 (+ i 1)))))
                     (=> a!1 (inv a1 i1 N)))))

(assert (forall ((a (Array Int Int)) (i Int) (N Int) (i1 Int))
                (=> (and (inv a i N) (>= i N) (<= 0 i1) (< i1 N) (> (select a i1) i1)) false)))

(check-sat)
