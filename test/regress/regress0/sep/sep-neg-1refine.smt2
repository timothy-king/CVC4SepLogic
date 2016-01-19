; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)

(declare-const x (Ref Int))
(declare-const y (Ref Int))
(declare-const z (Ref Int))

(declare-const a Int)
(declare-const b Int)

(assert (not (sep (pto x a) (pto y b))))
(assert (sep (pto x a) (pto z b)))

; sat with model where y != z
(check-sat)