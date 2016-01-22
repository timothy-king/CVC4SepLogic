; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(declare-fun x () (Ref Int))
(assert (wand (emp 0) (pto x 3)))
(check-sat)

