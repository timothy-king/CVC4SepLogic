; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)

(declare-const x (Ref Int))
(declare-const a Int)

(declare-const y (Ref Int))
(declare-const b Int)

(assert (or (pto x a) (sep (pto x a) (pto y b))))
(assert (or (not (pto x a)) (sep (not (pto x a)) (not (pto y b)))))

(check-sat)
