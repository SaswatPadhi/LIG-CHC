; SMT 2
; Generated for Z3
(set-info :source "")
(set-option :produce-models true)
; find_symbols
(declare-fun |loop_invariant| ((_ BitVec 32) (_ BitVec 32)) Bool)
; set_to true
(assert (forall ((|loop_example::y| (_ BitVec 32))) (forall ((|loop_example::x| (_ BitVec 32))) (=> (and (and (bvsge |loop_example::x| (_ bv0 32)) (bvsge |loop_example::y| (_ bv0 32))) (bvsle |loop_example::y| |loop_example::x|)) (|loop_invariant| |loop_example::x| |loop_example::y|)))))
; set_to true
(assert (forall ((|loop_example::y| (_ BitVec 32))) (forall ((|loop_example::x| (_ BitVec 32))) (=> (and (|loop_invariant| |loop_example::x| |loop_example::y|) (not (not (= |loop_example::y| (_ bv0 32))))) (bvsge |loop_example::x| (_ bv0 32))))))
; set_to true
(assert (forall ((|loop_example::y| (_ BitVec 32))) (forall ((|loop_example::x| (_ BitVec 32))) (=> (and (|loop_invariant| |loop_example::x| |loop_example::y|) (not (not (not (= |loop_example::y| (_ bv0 32)))))) (|loop_invariant| (bvsub |loop_example::x| (_ bv1 32)) (bvsub |loop_example::y| (_ bv1 32)))))))
(check-sat)