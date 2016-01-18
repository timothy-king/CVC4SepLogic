(set-logic ALL_SUPPORTED)

(declare-fun x () (Ref Int))

(assert (wand (pto x 1) (pto x 1)))
(check-sat)