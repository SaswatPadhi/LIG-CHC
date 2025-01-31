(set-logic HORN)
(set-info :source "")
(set-option :produce-models true)
; find_symbols
(declare-fun |loop_invariant| (Int) Bool)
(assert (forall ((|loop_example::x| Int))
          (=> (>= |loop_example::x| 0)  (|loop_invariant| |loop_example::x|))))
(assert (forall ((|loop_example::x| Int))
          (=> (and (|loop_invariant| |loop_example::x|) (= |loop_example::x| 0))
              (<= |loop_example::x| 0))))
(assert (forall ((|loop_example::x| Int))
          (=> (and (|loop_invariant| |loop_example::x|) (not (= |loop_example::x| 0)))
              (|loop_invariant| (- |loop_example::x| 1)))))
(check-sat)
(get-model)