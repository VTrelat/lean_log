import LeanLog.CustomPrelude
import Mathlib.Data.Finmap

set_option linter.style.longLine false

abbrev Constant := String
abbrev Variable := Nat
abbrev FunctionSymbol := fun _:Nat ↦ String

inductive Term where
  | var : Variable → Term
  | const : Constant → Term
  | func (n : Nat) : (FunctionSymbol n) → (Fin n → Term) → Term
  deriving Inhabited

namespace Term

def toString : Term → (show_arity : Bool := false) → String
  | var v, _ => s!"x{v.toSubscriptString}"
  | const c, _ => c
  | func n f args, true =>
    s!"{f}[{n}]({String.intercalate ", " (List.ofFn (fun i ↦ Term.toString (args i)))})"
  | func n f args, false =>
    s!"{f}({String.intercalate ", " (List.ofFn (fun i ↦ Term.toString (args i) false))})"

instance : ToString Term := ⟨Term.toString⟩

def Vars : Term → Finset Variable
  | .var v => {v}
  | .const _ => ∅
  | .func n f args => (List.ofFn (fun i ↦ Term.Vars (args i))).foldl (· ∪ ·) ∅

def size : Term → Nat
  | .var v => 0
  | .const c => 0
  | .func n f args => 1 + (List.ofFn (fun i ↦ (args i).size)).foldl (· + ·) 0

end Term

abbrev Atom (n : Nat) (r : String) := Fin n → Term

namespace Atom

def toString {n : ℕ} {r : String} : Atom n r → (show_arity : Bool := false) → String := fun a b ↦
  if b then
    s!"{r}[{n}]({String.intercalate ", " (List.ofFn (fun i ↦ Term.toString (a i)))})"
  else
    s!"{r}({String.intercalate ", " (List.ofFn (fun i ↦ Term.toString (a i) false))})"

def Vars {n : ℕ} {r : String} (a : Atom n r) : Finset Variable :=
  (List.ofFn (fun i ↦ Term.Vars (a i))).foldl (· ∪ ·) ∅

end Atom

inductive Formula where
  | atom (n : Nat) (r : String) : Atom n r → Formula
  | not : Formula → Formula
  | and : Formula → Formula → Formula
  | forall : Variable → Formula → Formula
  | eq : Formula → Formula → Formula
  deriving Inhabited

namespace Formula

section Syntax

scoped infix:50 " =₁ "  => Formula.eq
scoped infix:50 " ∧₁ "  => Formula.and
scoped prefix:70 "¬₁ "  => Formula.not
notation "∀₁" x "," f => Formula.forall x f

@[match_pattern]
def or (f1 f2 : Formula) : Formula := ¬₁ (¬₁ f1 ∧₁ ¬₁ f2)
scoped infix:55 " ∨₁ "  => Formula.or

@[match_pattern]
def implies (f1 f2 : Formula) : Formula := ¬₁ f1 ∨₁ f2
scoped infix:60 " →₁ "  => Formula.implies

@[match_pattern]
def «exists» (x : Variable) (f : Formula) : Formula := ¬₁ (∀₁ x, ¬₁ f)
scoped notation "∃₁" x "," f => Formula.exists x f

def toString : Formula → (show_arity : Bool := false) → String
  | atom _ _ a, b => a.toString b
  | eq f1 f2, b => "(" ++ toString f1 b ++ " = " ++ toString f2 b ++ ")"
  | implies f1 f2, b => "(" ++ toString f1 b ++ " → " ++ toString f2 b ++ ")"
  | or f1 f2, b => "(" ++ toString f1 b ++ " ∨ " ++ toString f2 b ++ ")"
  | «exists» x f, b => s!"∃ x{x.toSubscriptString}, {toString f b}"
  | not f, b => s!"¬ {toString f b}"
  | and f1 f2, b => "(" ++ toString f1 b ++ " ∧ " ++ toString f2 b ++ ")"
  | «forall» x f, b => s!"∀ x{x.toSubscriptString}, {toString f b}"

instance : ToString Formula := ⟨toString⟩

end Syntax

def Vars : Formula → Finset Variable
  | .atom _ _ a => a.Vars
  | .eq f1 f2 => (Vars f1) ∪ (Vars f2)
  | .not f => Vars f
  | .and f1 f2 => (Vars f1) ∪ (Vars f2)
  | .forall x f => (Vars f) ∪ {x}

def isClosed (f : Formula) : Prop := f.Vars = ∅

def size : Formula → Nat
  | .atom _ _ a => 0
  | .eq f1 f2 => 1 + f1.size + f2.size
  | .not f => 1 + f.size
  | .and f1 f2 => 1 + f1.size + f2.size
  | .forall x f => 1 + f.size

end Formula

-- (a)
#eval Term.func 2 "g" <| Fin.ofList [Term.const "a", Term.func 1 "f" <| Fin.ofList [Term.const "a"]]
-- (b)
#eval Term.func 1 "f" <| Fin.ofList [Term.func 2 "g" <| Fin.ofList [Term.func 1 "f" <| Fin.ofList [Term.var 0], Term.func 2 "g" <| Fin.ofList [Term.var 1, Term.func 1 "f" <| Fin.ofList [Term.const "a"]]]]
-- (c)
-- #eval Term.func 1 "f" <| Fin.ofList [Atom 1 "r" <| Fin.ofList [Term.var 0]] -- does not type check

-- (f)
#eval ∀₁ 0, ∃₁ 1, (¬₁ (atom 2 "s" <| Fin.ofList [.var 1, .const "b"]) ∧₁ (atom 1 "r" <| Fin.ofList [.const "a"])) →₁ (atom 2 "s" <| Fin.ofList [.func 1 "f" <| Fin.ofList [.const "a"], .var 0])

section Substitution

abbrev Substitution := Finmap (fun _ : Variable ↦ Term)

namespace Substitution

def dom (σ : Substitution) : Finset Variable := σ.keys

def eval (σ : Substitution) (x : Variable) : Term :=
  match σ.lookup x with
  | some t => t
  | none => Term.var x

def evalT (σ : Substitution) (t : Term) : Term :=
  match t with
  | .var v => σ.eval v
  | .const c => .const c
  | .func n f args => .func n f (fun i ↦ σ.evalT (args i))

end Substitution
end Substitution

theorem Term.size_of_subst_ge (σ : Substitution) (t : Term) : (σ.evalT t).size ≥ t.size := by
  induction t with
  | var v =>
    rw [Substitution.evalT, Substitution.eval]
    split <;> apply Nat.zero_le
  | const c => rw [Substitution.evalT]
  | func n f args ih =>
    rw [Substitution.evalT, Term.size, Term.size, ge_iff_le, Nat.add_le_add_iff_left]
    simp only [ge_iff_le] at ih
    apply List.foldl_sum_pointwise_le
    · intro i
      simp only [Fin.getElem_fin, List.getElem_ofFn]
      apply ih
    · rfl
    · simp only [List.length_ofFn]
      rfl
