(set-logic CHC_ALIA)

(synth-fun inv ((a (Array Int Int)) (i Int) (n Int)) Bool)

(constraint (forall ((a (Array Int Int)) (i Int) (N Int))
            (=> (and (= i 0) (<= i N)) (inv a i N))))

(constraint (forall ((a (Array Int Int)) (i Int) (N Int) (a1 (Array Int Int)) (i1 Int))
            (let ((a!1 (and (inv a i N) (< i N) (= a1 (store a i i)) (= i1 (+ i 1)))))
                 (=> a!1 (inv a1 i1 N)))))

(constraint (forall ((a (Array Int Int)) (i Int) (N Int) (i1 Int))
            (=> (and (>= i N) (inv a i N) (<= 0 i1) (< i1 i) (> (select a i1) N)) false)))

(check-synth)
