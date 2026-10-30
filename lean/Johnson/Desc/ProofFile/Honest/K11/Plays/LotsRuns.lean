-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsRuns.lean: the proofs of the five statements of
Johnson/Desc/ProofFile/Honest/K11/Plays/LotsRunsStatement.lean, to the letter. Lemmas; none of the
library's goals.

A FURTHER TEXT. The five lines of arithmetic in `firstRunFull` are this file's: a proof of
`SpentOfHalf` (MaskBridgeAllStatement.lean of this folder, a statement alone) is not in this
file: no theorem here states it.

How. The first run: `firstRun_count` (Honest/SumLaw/SumShown.lean), by the type; the count of the
merge's call is `mergeShapeSlots` (FrontSAtHead.lean of this folder). The end run: `endRun_length`
(Honest/SumLaw/FitsAt.lean) at the merge's call's one end value. The two corollaries: a list's
member below its length; a list of length one. The fifth: the texts' own first arm.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsRunsStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.FrontSAtHead
import Johnson.Desc.ProofFile.Honest.SumLaw.FitsAt
import Johnson.Desc.ProofFile.Honest.SumLaw.SumShown

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.Part.MaskedSum (ownSlots Call.all Call.endsN)
open ProofFile.Honest.SumLaw (firstRun endRun endRun_length firstRun_count)

/-- **The first run has 2 lk + 2 members.** -/
theorem firstRunFull : FirstRunFull := by
  intro W₀ Rc Xi Tr X P claims weights c
  have h1 : (firstRun c.2.1).length = ownRun (headMergeShape P.lay.lk) := firstRun_count c.2.1
  have h2 := mergeShapeSlots P.lay.lk
  have h3 : (headMergeShape P.lay.lk).endsN = 1 := rfl
  have h4 : ownRun (headMergeShape P.lay.lk) = 0 + ownSlots (headMergeShape P.lay.lk).all := rfl
  omega

/-- **The end run has one member.** -/
theorem endRunOne : EndRunOne := by
  intro W₀ Rc Xi Tr X P claims weights c
  exact endRun_length c.2.1 ⟨1, 1⟩ rfl

/-- **Inside its guard the first text reads a member of the first run.** -/
theorem maskLotReads : MaskLotReads := by
  intro W₀ Rc Xi Tr X P claims weights c ν₀ place h1 h2
  have hl := firstRunFull W₀ Rc Xi Tr X P claims weights c
  have hi : place - ν₀ < (firstRun c.2.1).length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- **The second text reads the end run's one member.** -/
theorem indexLotReads : IndexLotReads := by
  intro W₀ Rc Xi Tr X P claims weights c
  have hl := endRunOne W₀ Rc Xi Tr X P claims weights c
  cases h : endRun c.2.1 with
  | nil =>
    rw [h] at hl
    cases hl
  | cons a t =>
    rw [h] at hl
    cases t with
    | nil => rfl
    | cons b u => cases hl

/-- **Where the row is handed nothing both texts are silent.** -/
theorem lotsSilent : LotsSilent := by
  intro Bk W₀ Rc Xi Tr X ch pl P claims weights n ν₀ n' r p k e he w hd mask row place
  constructor
  · show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
      | .error _ => none
      | .ok c => _) = _
    rw [he]
  · show (match k11Lent Bk (Rc := Rc) (Tr := Tr) X ch pl P claims weights k with
      | .error _ => none
      | .ok c => _) = _
    rw [he]

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.firstRunFull
#print axioms ProofFile.Honest.K11.endRunOne
#print axioms ProofFile.Honest.K11.maskLotReads
#print axioms ProofFile.Honest.K11.indexLotReads
#print axioms ProofFile.Honest.K11.lotsSilent
