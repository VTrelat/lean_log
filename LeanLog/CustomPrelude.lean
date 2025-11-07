import Batteries.CodeAction

import Aesop

import Mathlib.Tactic.Conv
import Mathlib.Tactic.Clean
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.Monotonicity
import Mathlib.Tactic.FindSyntax
-- import Mathlib.Tactic.LiftLets
-- import Mathlib.Tactic.ExtractLets
import Batteries.Tactic.SeqFocus

import Mathlib.Util.WhatsNew
import Mathlib.Util.Delaborators
import Mathlib.Util.Superscript
import Mathlib.Util.AssertNoSorry

import Mathlib.Tactic.Linter

import LeanSearchClient

import Mathlib.Data.Finset.Basic

set_option autoImplicit false

def Nat.induction₂ {P : Nat → Prop} (h0 : P 0) (h1 : P 1)
  (hstep : ∀ n, P n → P (n + 1) → P (n + 2)) {n} : P n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      cases n with
      | zero => exact h1
      | succ n =>
        apply hstep
        · apply ih
          apply Nat.lt_add_right
          apply Nat.lt_add_one
        · apply ih
          apply Nat.lt_add_one


def Nat.induction₆ {C : Nat → Prop}
  (h0 : C 0) (h1 : C 1) (h2 : C 2) (h3 : C 3) (h4 : C 4) (h5 : C 5)
  (hstep : ∀ n, C n → C (n + 1) → C (n + 2) → C (n + 3) → C (n + 4) → C (n + 5) → C (n + 6)) :
    ∀ n, C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      cases n with
      | zero => exact h1
      | succ n =>
        cases n with
        | zero => exact h2
        | succ n =>
          cases n with
          | zero => exact h3
          | succ n =>
            cases n with
            | zero => exact h4
            | succ n =>
              cases n with
              | zero => exact h5
              | succ n =>
                apply hstep <;> apply ih <;> omega

def Fin.ofList {α} (l : List α) : (Fin l.length) → α := (l[·])


theorem List.foldl_sum_pointwise_le {xs ys : List Nat} {a b}
  (hys : xs.length ≤ ys.length)
  (h : ∀ i : Fin xs.length, xs[i] ≤ ys[i]) (hab : a ≤ b) :
    xs.foldl (· + ·) a ≤ ys.foldl (· + ·) b := by
  set n := xs.length
  induction hn : n generalizing a b xs ys with
  | zero =>
    subst n
    rw [List.length_eq_zero_iff] at hn
    subst xs
    cases ys with
    | nil =>
      simpa only [List.foldl_nil]
    | cons y ys =>
      rw [List.foldl_nil, List.foldl_cons, Nat.add_comm,
        ←List.foldl_cons, List.foldl_assoc_comm_cons]
      exact Nat.le_add_right_of_le hab
  | succ m ih =>
    subst n
    obtain ⟨x, xs, rfl⟩ := List.exists_of_length_succ xs hn
    rw [List.length_cons, Nat.add_right_cancel_iff] at hn
    rw [List.length_cons] at hys
    cases ys with
    | nil =>
      contradiction
    | cons y ys =>
      rw [List.foldl_cons, List.foldl_cons]
      simp only [length_cons, Nat.add_le_add_iff_right] at hys
      apply ih hys
      · intro i
        exact h i.succ
      · apply Nat.add_le_add hab
        exact h ⟨0, by exact Nat.zero_lt_succ xs.length⟩
      · exact hys
      · exact hn
