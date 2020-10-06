(set-logic CHC_LIA)

(set-info :source )

(set-option :produce-models true)

(synth-fun _VAR_0_ ((x_0 Int)) Bool)

(constraint (forall ((_VAR_1_ Int)) (=> (>= _VAR_1_ 0) (_VAR_0_ _VAR_1_))))

(constraint (forall ((_VAR_1_ Int)) (=> (and (_VAR_0_ _VAR_1_) (= _VAR_1_ 0)) (<= _VAR_1_ 0))))

(constraint (forall ((_VAR_1_ Int)) (=> (and (_VAR_0_ _VAR_1_) (not (= _VAR_1_ 0))) (_VAR_0_ (- _VAR_1_ 1)))))

(check-synth)
