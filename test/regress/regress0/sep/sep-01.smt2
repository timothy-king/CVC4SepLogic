(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (sep (pto x a) (pto y b)))

(assert (= x y))

(check-sat)