-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsA.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for four families of
sub-protocols: the three of the kind K9 in each of the 25 segments, and K5 in each of the 12
attention segments. 87 of the 358 numbers. Each lemma has the form that `head_hK_of_families`
(SteppedYes.lean) takes: at the sub-protocol at the number, every `StepYes` gives the clause of its
place's kind at its place. The proofs call the lemmas of the authors of these kinds. No definition.

  1  `fHead_keeps_bat`, `fHead_keeps_eq`, `fHead_keeps_shut`   K9, by `k9KeepsAt_step_bat`,
     `k9KeepsAt_step_eq`, `k9KeepsAt_step_shut` and `kind_bat_at`, `kind_eq_at`, `kind_shut_at`
     (Johnson/Desc/ProofFile/Honest/K9/KeepsAtPlace.lean)
  2  `fHead_keeps_k5`   K5, by `k5KeepsAt_payer_head`
     (Johnson/Desc/ProofFile/Honest/K5/Law/KeepsMT.lean)

Limits.
  * No hypothesis beside the library's `AtMgA` and the range of the segment's number. That a
    `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.K5.Law.KeepsMT

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At the batching of segment `l`. -/
theorem fHead_keeps_bat {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  rw [ProofFile.Honest.K9.kind_bat_at h hl hb]
  obtain ⟨R, c, -, hstep⟩ := hy
  exact ProofFile.Honest.K9.k9KeepsAt_step_bat h hl 0 hb ⟨R, c, c.length, hstep⟩

/-- At the one equation of segment `l`. -/
theorem fHead_keeps_eq {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have hb' : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 0]? = some blk := hb
  rw [ProofFile.Honest.K9.kind_eq_at h hl hb']
  obtain ⟨R, c, -, hstep⟩ := hy
  exact ProofFile.Honest.K9.k9KeepsAt_step_eq h hl 0 hb' ⟨R, c, c.length, hstep⟩

/-- At the shut of segment `l`. -/
theorem fHead_keeps_shut {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 6]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have hb' : cF.blocksInOrder[14 * l + IM.nAt l + 4 + 2]? = some blk := hb
  rw [ProofFile.Honest.K9.kind_shut_at h hl hb']
  obtain ⟨R, c, -, hstep⟩ := hy
  exact ProofFile.Honest.K9.k9KeepsAt_step_shut h hl 0 hb' ⟨R, c, c.length, hstep⟩

/-- At K5's sub-protocol of attention segment `2 * g + 1`. -/
theorem fHead_keeps_k5 {g : Nat} (hg : g < 12) :
    ∀ blk, cF.blocksInOrder[14 * (2 * g + 1) + 2 + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have hp := head_place_hear h (l := 2 * g + 1) (i := 2) (k := .K5) (by omega)
    (head_kind_att hg rfl) hb
  have hk : blk.place.kind = .K5 := by rw [hp]
  rw [hk]
  exact ProofFile.Honest.K5.k5KeepsAt_payer_head h hg blk hb s s' hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_bat
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_eq
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_shut
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k5
