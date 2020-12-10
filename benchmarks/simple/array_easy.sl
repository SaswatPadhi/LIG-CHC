(set-logic CHC_ALIA)

(synth-fun inv ((x_0 (Array Int Int)) (x_1 Int) (x_2 Int)) Bool)

(constraint (forall ((a (Array Int Int)) (N Int)) (=> (< 0 N) (inv a 0 N))))

(constraint (forall ((a (Array Int Int)) (i Int) (N Int) (a1 (Array Int Int)) (i1 Int))
                    (let ((a!1 (and (inv a i N) (< i N) (= a1 (store a i i)) (= i1 (+ i 1)))))
                         (=> a!1 (inv a1 i1 N)))))

(constraint (forall ((a (Array Int Int)) (i Int) (N Int) (i1 Int))
                    (=> (and (inv a i N) (>= i N) (<= 0 i1) (< i1 N) (> (select a i1) i1)) false)))

(check-synth)
