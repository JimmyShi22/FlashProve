-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsE.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for K6's sub-protocol,
number 341. The lemma has the form that `head_hK_of_families` (SteppedYes.lean) takes. The proof
calls two lemmas of the authors of that kind: `P4.k6_member_at_mg`
(Johnson/Desc/Kinds/Law/K6WayUpAtSeat.lean) says which sub-protocol stands at 341, and
`k6_keeps_of_member_step` (Johnson/Desc/K6/Honest/Law/KeepsMember.lean) gives the clause from its
step. No definition.

  1  `fHead_keeps_k6`   the lemma

Limits.
  * That a `StepYes` exists at any state is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction` (FirstAt.lean says
    which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.K6.Honest.Law.KeepsMember
import Johnson.Desc.Kinds.Law.K6WayUpAtSeat

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

/-- At K6's sub-protocol, number 341. -/
theorem fHead_keeps_k6 :
    ∀ blk, cF.blocksInOrder[341]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have hb' : cF.blocksInOrder[14 * 24 + 3 + 2]? = some blk := hb
  rw [head_place_hear h (l := 24) (i := 3) (k := .K6) (by omega) rfl hb']
  obtain ⟨b, hfl, M⟩ := P4.k6_member_at_mg h.toAtMg
  obtain rfl : b = blk := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨R, c, -, hstep⟩ := hy
  exact VerifiableInference.Desc.Kinds.Head.Honest.k6_keeps_of_member_step M hstep

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k6
