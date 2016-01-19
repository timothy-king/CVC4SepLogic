; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(set-info :status sat)
(declare-fun x () Int)

(assert (sep (= x 0) (not (= x 5))))

(declare-fun y () (Ref Int))
(assert (pto y 0))
(check-sat)