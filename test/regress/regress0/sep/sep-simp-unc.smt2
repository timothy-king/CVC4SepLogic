(set-logic ALL_SUPPORTED)

(declare-sort U 0)
(declare-fun x () (Ref U))
(declare-fun y () (Ref U))
(declare-fun a () U)
(declare-fun b () U)

(assert (not (sep (not (pto x a)) (pto y b))))
(check-sat)