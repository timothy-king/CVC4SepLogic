(set-logic ALL_SUPPORTED)
(set-info :status sat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(assert (and
        (not (sep (not (pto x a)) (pto y b) ))  
        (sep (pto x a) (pto y b))
  )
)

(check-sat)
