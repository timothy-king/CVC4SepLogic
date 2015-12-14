(set-logic ALL_SUPPORTED)
(set-info :status sat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (not (pto x a)))
(assert (sep (pto x a) (pto z b)))

(check-sat)