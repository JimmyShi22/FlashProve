-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsC.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for the two lookups (K3) in
each of the 25 segments. 50 of the 358 numbers. FHeadKeepsA.lean and FHeadKeepsB.lean have 113
others. The lemma has the form that `head_hK_of_families` (SteppedYes.lean) takes. The proof calls
`keeps_at_link` (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean) of the authors of that
kind. No definition.

  1  `fHead_keeps_k3`   the lemma

Limits.
  * No hypothesis beside the library's `AtMgA` and the range of the segment's number. That a
    `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At the lookup of segment `l`: on the calls (`d = false`) or on the digits (`d = true`). -/
theorem fHead_keeps_k3 {l : Nat} (hl : l < 25) (d : Bool) :
    ∀ blk, cF.blocksInOrder[borderOf l d]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' :=
  fun blk hb s s' hy =>
    ProofFile.Honest.K3.Law.AtThr.keeps_at_link h l hl d (fHead Zp cF G take P11 p12 P13)
      (fHead_K3 Zp cF G take P11 p12 P13) blk hb 0 s s' hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k3
