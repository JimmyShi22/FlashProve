-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/CutNums.lean: from the written cut of the proof file's first chain
(`cutFirstFull`, CutLit.lean) to the closed numbers of the 25 code switches (`n0At`,
Johnson/Top/H0/K2Hears/PlaceNums.lean): at a list of sub-protocols with that cut, the oracle
messages told in front of the switch into group l are `n0At l`, and the sub-protocol at the switch's
number bears the kind K2 and the switch's name. Statements and proofs; no definition.

  `n0_of_cut`       toldBefore bs (14 l + 2) = n0At l for l = 1 … 23; at 339: n0At 24; at 353: n0At
    25
  `n0_of_row`       the same from an accept of the row for the proof file's entry tests (`cutRow`)
  `place_of_cut`    the place and the name of the sub-protocol number k are the written row's
  `switch_names`    the names at the 25 numbers, written out: a closed fact, by Lean's kernel
Limits. Those of CutTest.lean and PlaceNums.lean. That the number of messages in the verifier's
state is what the sub-protocols in front have told is not shown here. The full size alone.
Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.Desc.Ok.PlanWritten.ToldTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open VerifiableInference.Desc
open VerifiableInference.Desc.First.K2 (n0At)

variable {S Cl : Type}

/-- **At the written cut the messages told in front of the switch into group l are `n0At l`.** -/
theorem n0_of_cut {bs : List (Block S Cl)} (h : cutOf bs = cutFirstFull) :
    (∀ l, 1 ≤ l → l ≤ 23 → toldBefore bs (14 * l + 2) = n0At l) ∧
      toldBefore bs 339 = n0At 24 ∧ toldBefore bs 353 = n0At 25 := by
  have H := toldPinned_eq (told_of_cut h)
  rw [cuts_are_n0] at H
  refine ⟨fun l h1 h2 => ?_, ?_, ?_⟩
  · exact H (14 * l + 2, n0At l) (List.mem_append_left _ (List.mem_map.2
      ⟨l, by rw [List.mem_range'_1]; omega, rfl⟩))
  · exact H (339, n0At 24) (List.mem_append_right _ (by simp))
  · exact H (353, n0At 25) (List.mem_append_right _ (by simp))

/-- The same from the row's accept. -/
theorem n0_of_row {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} (h : cutRow F Z = true) :
    (∀ l, 1 ≤ l → l ≤ 23 → toldBefore F.first.blocksInOrder (14 * l + 2) = n0At l) ∧
      toldBefore F.first.blocksInOrder 339 = n0At 24 ∧ toldBefore F.first.blocksInOrder 353 = n0At 25 :=
  n0_of_cut (cut_of_row h).1

/-- The name and the place of the sub-protocol number k are the written row's. -/
theorem place_of_cut {bs : List (Block S Cl)} (h : cutOf bs = cutFirstFull) (k : Nat) :
    (bs[k]?).map (fun b => (b.name, b.place)) = (cutFirstFull[k]?).map fun r => (r.1, r.2.1) := by
  rw [← h, row_at, Option.map_map]
  rfl

set_option maxRecDepth 1000000 in
/-- The names at the 25 numbers. -/
theorem switch_names : switchCuts.map (fun x => (cutFirstFull[x.1]?).map (·.1)) =
    [some "A0:1", some "G1:1", some "A1:1", some "G2:1", some "A2:1", some "G3:1", some "A3:1",
      some "G4:1", some "A4:1", some "G5:1", some "A5:1", some "G6:1", some "A6:1", some "G7:1",
      some "A7:1", some "G8:1", some "A8:1", some "G9:1", some "A9:1", some "G10:1", some "A10:1",
      some "G11:1", some "A11:1", some "H:2", some "F:1"] := by
  decide +kernel

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.n0_of_cut
#print axioms VerifiableInference.PlanWritten.n0_of_row
#print axioms VerifiableInference.PlanWritten.place_of_cut
#print axioms VerifiableInference.PlanWritten.switch_names
