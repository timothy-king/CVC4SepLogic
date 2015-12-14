(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (sep (pto x a) true)
        (sep (pto y (+ a 1)) true)
))
(assert (= x y))

(check-sat)