-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/ToldAtCut.lean: WHERE A LIST OF SUB-PROTOCOLS HAS THE WRITTEN CUT, WHAT
IT TELLS HAS THE WRITTEN COUNTS; so the premise hT of maskNum_in_scope
(Johnson/Desc/Sound/K11Tests/MaskSixInScope.lean) falls to "the cut is the written one", which
other files' theorem on the kind K11 (Johnson/K11R/) has as its own premise hc. Two joinings, by
calls alone: no law is typed here.

  counts_of_cut    cutOf bs = cutFirstFull → CountsAre (Sound.toldOf bs) ∧ TreesAre (the same)
  maskNum_at_cut   maskNum_in_scope with hc in hT's place, at told := Sound.toldOf bs

THE LINKS, ALL IN THE LIBRARY: First.toldOf bs = toldCut under hc (told_at_written,
Johnson/Desc/First/CutWritten.lean; toldCut is by its definition the written cut's rows' told trees,
laid flat) · CountsAre and TreesAre at that list (countsAre_cut, treesAre_cut,
Johnson/HB/LLHARD/CountsAtCut.lean). Sound.toldOf and First.toldOf are one function: that stands as
a theorem twice (told_two, Johnson/P5J/K03PiecesAt.lean; At.told_is, Johnson/P5J/LettersAt.lean);
here it is one step inside a proof (List.flatMap_id), so that this file's cone stays small.

Limits. That a list of sub-protocols has the written cut is a premise (a row of the entry tests'
list of thirteen rows). The full size alone. Nothing on soundness.

-/
import Johnson.Desc.Sound.K11Tests.MaskSixInScope
import Johnson.Desc.First.CutWritten
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Desc.Sound.PieceFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers flatPlacesOf told_at_written)
open VerifiableInference.Desc.First.MergeLaw (firstCount momentCount)
open VerifiableInference.Desc.K13.Law (CountsAre TreesAre countsAre_cut treesAre_cut)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open VerifiableInference.PlanWritten (madePinnedAt cutFirstFull)

/-- **Where the cut is the written one, what is told has the written counts.** -/
theorem counts_of_cut {St Cl : Type} {bs : List (Block St Cl)}
    (hc : VerifiableInference.PlanWritten.cutOf bs = cutFirstFull) :
    CountsAre (Sound.toldOf bs) ∧ TreesAre (Sound.toldOf bs) := by
  have e1 : Sound.toldOf bs = First.toldOf bs := by
    unfold Sound.toldOf First.toldOf
    exact List.map_congr_left fun _ _ => List.flatMap_id
  rw [e1, (told_at_written hc).2]
  exact ⟨countsAre_cut, treesAre_cut⟩

/-- **maskNum, with "the cut is the written one" in hT's place.** -/
theorem maskNum_at_cut {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) {G₀ : ProofFile.Ground}
    (hG : G₀.first.shape = Z.first.shape) (N : Numbers) {St Cl : Type}
    {bs : List (Block St Cl)} (hc : VerifiableInference.PlanWritten.cutOf bs = cutFirstFull) :
    181 + (firstCount Z.first.shape 24 + 1) +
        (momentCount G₀.first.shape 24 1 + momentCount G₀.first.shape 24 2) =
      (N.withTold (flatPlacesOf linksFull true) (Sound.toldOf bs)).msgsAt (some mergeAt) + 0 :=
  maskNum_in_scope hW h hy hG N (counts_of_cut hc).1

end LT28.K11Tests

#print axioms LT28.K11Tests.counts_of_cut
#print axioms LT28.K11Tests.maskNum_at_cut
