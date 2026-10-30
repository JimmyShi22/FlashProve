-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/GuardsShape.lean: kind K13, the members' batching: THE NINE GUARDS
ON THE VERIFIER's STATE (`K13Guards`, Debts.lean of this folder) ARE ONE TEST WITH CODE ON THE
STATE's SHAPE (`readySh` at `shOf`, Johnson/Desc/K13/Honest/Shape.lean). One statement with its
proof, and two corollaries.
Main names:
  `guards_iff`: **the statement.**
  `guards_of_return`: where the kind's own sub-protocol returns, the guards held in front.
  `guards_congr`: two states of one shape pass the guards alike.

What is not claimed. That the guards hold at a state of a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.Debts
import Johnson.Desc.K13.Honest.ShapeBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where atM3)
open VerifiableInference.Desc.K13.Honest (readySh shOf ready_of_shape shape_of_nine shape_of_return)

/-- **The nine guards are the test on the state's shape.** -/
theorem guards_iff (P : Where) (s : S) : K13Guards P s ↔ readySh P (shOf s) = true := by
  constructor
  · rintro ⟨⟨f, a1⟩, a2, a3, a4, a5, a6, ⟨t, a7⟩, a8, ⟨msg, a9⟩⟩
    exact shape_of_nine a1 a2 a3 a4 a5 a6 a7 a8 a9
  · intro h
    obtain ⟨f, t, msg, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ready_of_shape h
    exact ⟨⟨f, a1⟩, a2, a3, a4, a5, a6, ⟨t, a7⟩, a8, ⟨msg, a9⟩⟩

/-- Where the kind's own sub-protocol returns, the guards held in front. -/
theorem guards_of_return {Cl : Type} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    K13Guards P s :=
  (guards_iff P s).2 (shape_of_return h)

/-- Two states of one shape pass the guards alike. -/
theorem guards_congr (P : Where) {s u : S} (e : shOf s = shOf u) :
    K13Guards P s ↔ K13Guards P u := by
  rw [guards_iff, guards_iff, e]

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.guards_iff
#print axioms ProofFile.Honest.K13.guards_of_return
#print axioms ProofFile.Honest.K13.guards_congr
