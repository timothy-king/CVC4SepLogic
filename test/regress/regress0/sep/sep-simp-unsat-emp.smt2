(set-logic ALL_SUPPORTED)
(set-info :status unsat)

(declare-sort U 0)
(declare-fun x () (Ref U))
(declare-fun y () (Ref U))
(declare-fun a () U)
(declare-fun b () U)

(assert (emp x))
(assert (sep (pto x a) (pto y b)))
(check-sat)
