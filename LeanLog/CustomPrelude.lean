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
