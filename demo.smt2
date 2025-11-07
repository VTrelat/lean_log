(set-logic UF)
(declare-sort U 0)

(declare-fun p (U) Bool)
(declare-fun q (U U) Bool)
(declare-fun r (U U) Bool)
(declare-fun g (U U) U)

(declare-const x1 U)
(declare-const y1 U)
(declare-const z1 U)

; q(z1,y1) ∨ r(x1,y1) ∨ p(g(x1,y1)))
(assert (or (q z1 y1) (r x1 y1) (p (g x1 y1))))

; ¬p(y2) ∨ ¬r(x2,z2) ∨ q(y2,x2)
(declare-const x2 U)
(declare-const y2 U)
(declare-const z2 U)
(assert (or (not (p y2)) (not (r x2 z2)) (q y2 x2)))

; ¬r(y3,x3) ∨ p(g(z3,x3))
(declare-const x3 U)
(declare-const y3 U)
(declare-const z3 U)
(assert (or (not (r y3 x3)) (p (g z3 x3))))

; ¬p(g(y4,y4))
(declare-const y4 U)
(assert (not (p (g y4 y4))))

; ¬q(x5,Z(y5))
(declare-const x5 U)
(declare-const y5 U)
(declare-fun Z (U) U)
(assert (not (q x5 (Z y5))))

(check-sat)