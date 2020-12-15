(set-logic HORN)

; Explain why this simple invariant from array_1 doesn't work:
;   - it's not enough to simply have (<= i n) in the beginning (precondition),
;   - we also need to make sure that it is preserved at each loop iteration
;
;(define-fun inv ((a (Array Int Int)) (i Int) (n Int)) Bool
;  (forall ((j Int)) (=> (and (<= 0 j) (< j i)) (= (select a j) j))))

(define-fun inv ((a (Array Int Int)) (i Int) (n Int)) Bool
  (and (<= i n) (forall ((j Int)) (=> (and (<= 0 j) (< j i)) (= (select a j) j)))))

; Show that LIG-CHC infers a simpler invariant :)

(assert (forall ((a (Array Int Int)) (i Int) (N Int))
        (=> (and (= i 0) (<= i N)) (inv a i N))))

(assert (forall ((a (Array Int Int)) (i Int) (N Int) (a1 (Array Int Int)) (i1 Int))
                (let ((a!1 (and (inv a i N) (< i N) (= a1 (store a i i)) (= i1 (+ i 1)))))
                     (=> a!1 (inv a1 i1 N)))))

(assert (forall ((a (Array Int Int)) (i Int) (N Int) (i1 Int))
                (=> (and (>= i N) (inv a i N) (<= 0 i1) (< i1 i) (> (select a i1) N)) false)))

(check-sat)
