(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (not (sep (not (pto x a)) (not (pto y b)) (not (sep (pto x a) (pto y b))) (not (emp x)) ))
        (sep (pto x a) (pto y b))
  )
)

(check-sat)
