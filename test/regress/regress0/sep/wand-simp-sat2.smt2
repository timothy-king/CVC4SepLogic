; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(declare-fun x () (Ref Int))
(assert (wand (pto x 1) (pto x 3)))
(check-sat)