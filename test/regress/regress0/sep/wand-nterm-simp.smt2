; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic ALL_SUPPORTED)
(declare-fun x () (Ref Int))
(assert (wand (emp x) (pto x 3)))
(check-sat)

