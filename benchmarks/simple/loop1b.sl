(set-info :source )

(set-option :produce-models true)

(synth-fun _VAR_0_ ((x_0 (_ BitVec 32)) (x_1 (_ BitVec 32))) Bool)

(constraint (forall ((_VAR_1_ (_ BitVec 32))) (forall ((_VAR_2_ (_ BitVec 32))) (=> (and (and (bvsge _VAR_2_ (_ bv0 32)) (bvsge _VAR_1_ (_ bv0 32))) (bvsle _VAR_1_ _VAR_2_)) (_VAR_0_ _VAR_2_ _VAR_1_)))))

(constraint (forall ((_VAR_1_ (_ BitVec 32))) (forall ((_VAR_2_ (_ BitVec 32))) (=> (and (_VAR_0_ _VAR_2_ _VAR_1_) (not (not (= _VAR_1_ (_ bv0 32))))) (bvsge _VAR_2_ (_ bv0 32))))))

(constraint (forall ((_VAR_1_ (_ BitVec 32))) (forall ((_VAR_2_ (_ BitVec 32))) (=> (and (_VAR_0_ _VAR_2_ _VAR_1_) (not (not (not (= _VAR_1_ (_ bv0 32)))))) (_VAR_0_ (bvsub _VAR_2_ (_ bv1 32)) (bvsub _VAR_1_ (_ bv1 32)))))))

(check-synth)
