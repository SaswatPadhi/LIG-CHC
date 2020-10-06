(set-info :source )

(set-option :produce-models true)

(synth-fun _VAR_0_ ((x_0 Int) (x_1 Int)) Bool)

(constraint (forall ((_VAR_1_ Int) (_VAR_2_ Int)) (=> (and (and (>= _VAR_2_ 0) (>= _VAR_1_ 0)) (<= _VAR_1_ _VAR_2_)) (_VAR_0_ _VAR_2_ _VAR_1_))))

(constraint (forall ((_VAR_1_ Int) (_VAR_2_ Int)) (=> (and (_VAR_0_ _VAR_2_ _VAR_1_) (not (not (= _VAR_1_ 0)))) (>= _VAR_2_ 0))))

(constraint (forall ((_VAR_1_ Int) (_VAR_2_ Int)) (=> (and (_VAR_0_ _VAR_2_ _VAR_1_) (not (not (not (= _VAR_1_ 0))))) (_VAR_0_ (- _VAR_2_ 1) (- _VAR_1_ 1)))))

(check-synth)
