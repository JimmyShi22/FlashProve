-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- «Nat» is written for «ℕ» here (the same type: this file imports no library that has the sign). The two stand apart from Johnson/RunOne/KeyFillOn.lean, so that a file of evaluations can call them without that file's cone.
/-
Johnson/RunOne/KeyPlacedB.lean: Placed (Johnson/Desc/Key/KeyTies.lean) AS A PLAIN TEST, WITH ITS TIE.
  placedB       general in orc | place | off | at_ | the list of numbers
  placed_of_B   placedB … = true → Placed …   (one way)
OBJECT: Placed · USER: Johnson/RunOne/KeyFillOn.lean's on₁_of_tests' callers; the tie «all sixteen Bools ⟹ Tests₂» · LETTERS: all. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key

/-- Placed as a plain test. -/
def placedB (orc : Nat → Option Nat) (place : Nat → Option (Nat × Nat)) (off : Nat → Nat) (at_ : Where) (ks : List Nat) : Bool :=
  ks.all fun k => match orc k with
    | none => false
    | some o => match place o with
      | none => false
      | some t => decide (at_ k = (off t.1, t.2))

theorem placed_of_B (orc : Nat → Option Nat) (place : Nat → Option (Nat × Nat)) (off : Nat → Nat) (at_ : Where) (ks : List Nat) (h : placedB orc place off at_ ks = true) : Placed orc place off at_ ks := by
  intro k hk
  have h1 := List.all_eq_true.1 h k hk
  cases ho : orc k with
  | none => simp [ho] at h1
  | some o =>
    cases hp : place o with
    | none => simp [ho, hp] at h1
    | some t =>
      simp only [ho, hp, decide_eq_true_eq] at h1
      exact ⟨o, t, rfl, hp, h1⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.placed_of_B
