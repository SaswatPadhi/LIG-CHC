(set-logic CHC_ALIA)

(synth-fun inv ((x_0 (Array Int Int)) (x_1 Int) (x_2 Int) (x_3 Int)) Bool)

(constraint (forall ((a (Array Int Int)) (N Int)) (=> (< 0 N) (inv a 0 7 N))))

(constraint (forall ((a (Array Int Int)) (i Int) (val Int) (N Int) (a1 (Array Int Int)) (i1 Int))
                    (let ((a!1 (and (inv a i val N) (< i N) (= a1 (store a i val)) (= i1 (+ i 1)))))
                         (=> a!1 (inv a1 i1 val N)))))

(constraint (forall ((a (Array Int Int)) (i Int) (val Int) (N Int) (i1 Int))
                    (=> (and (inv a i val N) (>= i N) (<= 0 i1) (< i1 N) (> (select a i1) val)) false)))

(check-synth)
