import LeanLog.CustomPrelude

section Exercice1

open Classical in
example (mange_la_soupe : Prop) (regarder_la_tele : Prop)
  (consigne : ¬ mange_la_soupe → ¬ regarder_la_tele)
  (h : mange_la_soupe) :
    regarder_la_tele := by
  admit

end Exercice1

section Exercice2

def α (a b c : Prop) := ((a → b) ∧ ((c ∨ ¬b) → a)) → (b → c)

open Classical in
theorem ex2_2 : ∃ a b c, α a b c := by
  unfold α
  use False, False, True
  intros
  trivial

-- α n'est pas une tautologie
example : ∀ a b c, α a b c := by
  classical
  unfold α
  rintro a b c ⟨h₁, h₂⟩ h₃
  by_cases hc : c
  · admit
  · absurd hc -- on ne peut pas prouver c à partir de ¬c.
    admit

end Exercice2

section Exercice3

variable (x y z t : Bool)

def φ : Bool := (¬ x ∨ y) ∨ (z → (x ↔ y))
-- donner la table de vérité de φ

def φ_table : IO Unit := do
  println! "| x | y | z | φ |"
  println! "|---|---|---|---|"
  for x in [false, true] do
    for y in [false, true] do
      for z in [false, true] do
        println! "| {x.toNat} | {y.toNat} | {z.toNat} | {φ x y z |>.toNat} |"
-- #eval φ_table

example : (¬x → y) ∨ (x → ¬y) := by
  cases x with
  | false =>
    right
    intro
    contradiction
  | true =>
    left
    intro
    contradiction

example : (x ∧ y) ∨ (y ∧ z) ∨ (z ∧ x) := by
  cases x
  · simp -- non prouvable
    admit
  admit


example : ((x → y) ∧ (z → t)) → (x ∧ z → y ∧ t) := by
  rintro ⟨h₁, h₂⟩ ⟨rfl, rfl⟩
  specialize h₁ rfl
  specialize h₂ rfl
  exact ⟨h₁, h₂⟩

end Exercice3

section Exercice5
variable (a b : Prop)

example (h₁ : a → b) (h₂ : b → a) (h₃ : a ∨ b) : a ∧ b := by
  rcases h₃ with ha | hb
  · and_intros
    · exact ha
    · exact h₁ ha
  · and_intros
    · exact h₂ hb
    · exact hb

example (h₁ : a → b) (h₂ : a ∨ b) : b → a := by
  intro hb
  rcases h₂ with ha | _
  · exact ha
  · admit

example (h₁ : a → b) (h₂ : a ∨ b) : a ∨ ¬a := by
  exact Classical.em a

example (h₁ : a ∧ ¬b) (h₂ : ¬a ∧ b) : a := by
  obtain ⟨_, _⟩ := h₁
  obtain ⟨_, _⟩ := h₂
  contradiction

end Exercice5

section Exercice7
variable (p q r : Prop)

#check p ∧ ¬q
#check ¬p ∧ ¬q
#check p ∨ (q ∧ ¬p)
#check q → p
#check (q ∧ p) ∨ (q ∧ ¬p)

#check p ∧ r ∧ ¬q
#check p ∧ q ∧ ¬(q ∧ r)
#check ¬( r ∧ ¬p)
#check ¬(¬p ∧ q)
#check ¬((r ∨ q) ∧ ¬p)
#check ¬r ∧ ¬q ∧ p

end Exercice7

section Exercice8
variable (p q : Bool)

def sheffer : Bool := ¬(p ∧ q)
infix:60 " ∣ " => sheffer

def sheffer_table : IO Unit := do
  println! "| p | q | p ∣ q |"
  println! "|---|---|-------|"
  for x in [false, true] do
    for y in [false, true] do
      println! "| {x.toNat} | {y.toNat} |   {x ∣ y |>.toNat}   |"
#eval sheffer_table

theorem not_as_sheffer : (¬ p) = (p ∣ p) := by
  simp_rw [Bool.not_eq_true, sheffer, and_self, Bool.not_eq_true,
    Bool.decide_eq_false, Bool.not_eq_eq_eq_not, Bool.not_true]

theorem and_as_sheffer : (p ∧ q) = (p ∣ q) ∣ (p ∣ q) := by
  rw [←not_as_sheffer, Bool.not_eq_true, sheffer, decide_not, Bool.not_eq_false',
    ←Bool.and_eq_decide, Bool.and_eq_true]

theorem or_as_sheffer : (p ∨ q) = (p ∣ p) ∣ (q ∣ q) := by
  conv =>
    enter [2]
    rw [sheffer, decide_not, Bool.not_eq_true', ←Bool.and_eq_decide, Bool.and_eq_false_iff]
  simp only [sheffer, and_self, Bool.not_eq_true, Bool.decide_eq_false, Bool.not_eq_eq_eq_not,
    Bool.not_false]

theorem imp_as_sheffer : (p → q) = (p ∣ (q ∣ q)) := by
  simp [sheffer]
  constructor <;> intro h
  · cases p
    · left
      rfl
    · right
      exact h rfl
  · rcases h with rfl | h
    · rintro ⟨⟩
    · intro
      exact h

theorem iff_as_sheffer :
    (p ↔ q) = (((p ∣ (q ∣ q)) ∣ (q ∣ (p ∣ p))) ∣ ((p ∣ (q ∣ q)) ∣ (q ∣ (p ∣ p)))) := by
  simp [sheffer]
  constructor <;> intro h
  · subst p
    rw [Bool.eq_false_or_eq_true_self]
    trivial
  · rcases h with ⟨rfl | rfl, h | h⟩
    · exact h.symm
    · contradiction
    · contradiction
    · exact h

end Exercice8
