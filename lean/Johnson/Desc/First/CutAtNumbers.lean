-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/CutAtNumbers.lean: WHAT THE TABLE's NUMBERS READ OF THE SUB-PROTOCOLS, OFF
THEIR CUT: the places, what each sub-protocol tells, and how many rounds each declares are
functions of `cutOf bs` (Johnson/Desc/Ok/PlanWritten/CutTest.lean). Four theorems. A file beside
the table: it turns nothing of it.
Why. `Numbers.atBlocks` (Johnson/Desc/First/NumbersAtBlocks.lean) fills the table's numbers off
`blockPlaces bs` and `toldOf bs`. The verifier's entry tests are to compare `cutOf` of each chain
whole with one written list. Where that comparison accepts, both are then closed terms: a test on
the table's numbers that reads them becomes a closed fact on a written value.
  `blockPlaces_cut`: the places are the cut's second field.
  `toldOf_cut`: what each sub-protocol tells is its row's rounds that tell a tree, laid flat: by
  `toldRounds_flat` (Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean).
  `roundsLen_cut`: how many rounds each declares is the cut's third field.
  `told_at_cut`: **where `cutOf bs = C`: `blockPlaces bs` and `toldOf bs` are the two lists off
  C.**
Limits. By unfolding. `cutOf` is written `PlanWritten.cutOf` in the code: another `cutOf` (on a
list of entries) stands in this namespace. That a cut is the written one is the comparison's to
give. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.NumbersAtBlocks
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (toldRounds toldRounds_flat)

variable {St Cl : Type}

/-- The places are the cut's second field. -/
theorem blockPlaces_cut (bs : List (Block St Cl)) :
    blockPlaces bs = (PlanWritten.cutOf bs).map (·.2.1) := by
  unfold blockPlaces PlanWritten.cutOf
  rw [List.map_map]
  rfl

/-- What each sub-protocol tells is its row's rounds that tell a tree, laid flat. -/
theorem toldOf_cut (bs : List (Block St Cl)) :
    toldOf bs = (PlanWritten.cutOf bs).map fun r => r.2.2.2.2.1.flatMap (·.2) := by
  unfold toldOf PlanWritten.cutOf
  rw [List.map_map]
  exact List.map_congr_left fun b _ => (toldRounds_flat b).symm

/-- How many rounds each sub-protocol declares is the cut's third field. -/
theorem roundsLen_cut (bs : List (Block St Cl)) :
    bs.map (·.rounds.length) = (PlanWritten.cutOf bs).map (·.2.2.1) := by
  unfold PlanWritten.cutOf
  rw [List.map_map]
  rfl

/-- **Where the cut is C, the places and what is told are the two lists off C.** -/
theorem told_at_cut {bs : List (Block St Cl)}
    {C : List (String × Place × Nat × Nat × List (Nat × List Oracle) × List (Nat × Nat))}
    (h : PlanWritten.cutOf bs = C) :
    blockPlaces bs = C.map (·.2.1) ∧ toldOf bs = C.map fun r => r.2.2.2.2.1.flatMap (·.2) := by
  subst h
  exact ⟨blockPlaces_cut bs, toldOf_cut bs⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.blockPlaces_cut
#print axioms VerifiableInference.Desc.First.toldOf_cut
#print axioms VerifiableInference.Desc.First.roundsLen_cut
#print axioms VerifiableInference.Desc.First.told_at_cut
