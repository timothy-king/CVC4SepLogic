(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (and (sep (pto x a) (or (pto x a) (pto y b)))
       (sep (pto y b) (or (pto x a) (pto y b)))
    )
)

(assert (not (sep (pto x a) (pto y b))))

(check-sat)