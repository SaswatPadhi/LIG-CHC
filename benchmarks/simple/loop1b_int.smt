(set-logic HORN)
(set-info :source "")
(set-option :produce-models true)
; find_symbols
(declare-fun |loop_invariant| (Int Int) Bool)
; set_to true
(assert (forall ((|loop_example::y| Int) (|loop_example::x| Int))
                (=> (and (and (>= |loop_example::x| 0) (>= |loop_example::y| 0)) (<= |loop_example::y| |loop_example::x|))
                    (|loop_invariant| |loop_example::x| |loop_example::y|))))
; set_to true
(assert (forall ((|loop_example::y| Int) (|loop_example::x| Int))
                (=> (and (|loop_invariant| |loop_example::x| |loop_example::y|) (not (not (= |loop_example::y| 0))))
                    (>= |loop_example::x| 0))))
; set_to true
(assert (forall ((|loop_example::y| Int) (|loop_example::x| Int))
                (=> (and (|loop_invariant| |loop_example::x| |loop_example::y|) (not (not (not (= |loop_example::y| 0)))))
                    (|loop_invariant| (- |loop_example::x| 1) (- |loop_example::y| 1)))))
(check-sat)
(get-model)