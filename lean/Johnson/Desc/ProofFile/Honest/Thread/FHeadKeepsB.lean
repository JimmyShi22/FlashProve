-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsB.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for two more families of
sub-protocols: the closing (K10) in each of the 25 segments, and K13's sub-protocol at number 355.
26 of the 358 numbers. FHeadKeepsA.lean has 87 others. Each lemma has the form that
`head_hK_of_families` (SteppedYes.lean) takes. The proofs call the lemmas of the authors of these
kinds. No definition.

  1  `fHead_keeps_k10`   K10, by `keeps_at_place` (Johnson/Desc/K10/Honest/KeepsSeat.lean) and the
     library's `LPFK10.k10_place_w` (Johnson/LPFK10R/CloseShare.lean)
  2  `fHead_keeps_k13`   K13, by `k13_keeps_at` and `m3_member_place`
     (Johnson/Desc/ProofFile/Honest/K13/KeepsFromStepAt.lean, FromThreadAt.lean), with the argument
     `P13` of `fHead` at the library's `h.𝔇.P13`

Limits.
  * No hypothesis beside the library's `AtMgA` and the range of the segment's number. That a
    `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.K10.Honest.KeepsSeat
import Johnson.LPFK10R.CloseShare
import Johnson.Desc.ProofFile.Honest.K13.KeepsFromStepAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At the closing of segment `l`. -/
theorem fHead_keeps_k10 {l : Nat} (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have eL : LPFK10.LW = linksFull := by decide
  have eP : LPFK10.PW = P5J.At.ps := by
    show flatPlacesOf LPFK10.LW true = flatPlacesOf linksFull true
    rw [eL]
  obtain ⟨p, hp, hk⟩ := LPFK10.k10_place_w hl
  rw [eP] at hp
  have hp' : P5J.At.ps[14 * l + IM.nAt l + 5]? = some p := hp
  obtain ⟨b, hb', hbp, hd⟩ := ProofFile.Honest.K10.YesFree.keeps_at_place h _ p hp' hk
  obtain rfl : b = blk := Option.some.inj (hb'.symm.trans hb)
  rw [hbp, hk]
  obtain ⟨rs, gs, e⟩ := stepYes_decide hy
  exact hd s s' rs gs e

/-- At K13's sub-protocol, number 355. -/
theorem fHead_keeps_k13 :
    ∀ blk, cF.blocksInOrder[355]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 h.𝔇.P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  rw [ProofFile.Honest.K13.m3_member_place h hb]
  exact ProofFile.Honest.K13.k13_keeps_at h 0 blk hb s s' hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k10
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k13
