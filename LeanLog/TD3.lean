
inductive Formula
  | var : String → Formula
  | top : Formula
  | or : Formula → Formula → Formula
  | not : Formula → Formula
  deriving Inhabited, DecidableEq

def Formula.toString : Formula → String
  | .var x => x
  | .top => "⊤"
  | .or φ₁ φ₂ => "(" ++ φ₁.toString ++ " ∨ " ++ φ₂.toString ++ ")"
  | .not φ => "(~" ++ φ.toString ++ ")"
instance : ToString Formula where
  toString := Formula.toString

infixl:60 " ∨ " => Formula.or
prefix:70 "~" => Formula.not
notation "⊤" => Formula.top

def Formula.and (φ ψ : Formula) : Formula := ~(~φ ∨ ~ψ)
infixl:60 " ∧ " => Formula.and
def Formula.imp (φ ψ : Formula) : Formula := ~φ ∨ ψ
infixl:55 " ⇒ " => Formula.imp
def Formula.iff (φ ψ : Formula) : Formula := (φ ⇒ ψ) ∧ (ψ ⇒ φ)
infixl:50 " ⇔ " => Formula.iff

abbrev valuation := String → Bool

def Formula.eval : Formula → valuation → Bool
  | var x, δ => δ x
  | top, _ => true
  | or φ₁ φ₂, δ => (φ₁.eval δ) || (φ₂.eval δ)
  | not φ, δ => !φ.eval δ


def Formula.pushNeg : Formula → Formula
  | var x => var x
  | top => top
  | or φ₁ φ₂ => (φ₁.pushNeg).or (φ₂.pushNeg)
  | not (var x) => not (var x)
  | not top => not top
  | not (or φ₁ φ₂) => (not φ₁).pushNeg.and (not φ₂).pushNeg
  | not (not φ) => φ.pushNeg

open Formula in
#eval (~(var "p" ⇒ var "q")).pushNeg
