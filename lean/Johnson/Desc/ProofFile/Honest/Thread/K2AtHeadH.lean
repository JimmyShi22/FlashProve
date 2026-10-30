-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K2AtHeadH.lean: what an accepting step of the code switch (K2)
gives, under the library's hypothesis `AtMgA`, at number 339: the second sub-protocol of the output
head's segment. K2AtHead.lean has the kind's 24 other numbers. The library's `IM.k2_head_of`
(Johnson/IMR/K2Seat.lean) says that the sub-protocol there is a block of K2's table, seated alone.
`seated_is_pAt` (Johnson/Top/H0/K2Caller/PAtSeated.lean) says which of the three forms that block
has, together with the field `stands` of its parameter. The proof of the library's `k02_sits_pAt`
draws the same form in the same way. `k2Keeps_head` (Johnson/Desc/K2/Honest/KeepsAt.lean) of the
authors of K2's lemmas gives the clause. No definition.

  1  `k2_head_head`   at number 339: `K2Keeps` at a parameter that stands at the head's place

Limits.
  * That a `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.K2.Honest.KeepsAt
import Johnson.Top.H0.K2Caller.SitsAtP
import Johnson.P1K2R.SitsDoor
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.Top.H0.Opts.Links25AtHead
import Johnson.Road.K4.K4HeadWritten
import Johnson.IMR.FlatScope
import Johnson.IMR.MemberPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2 (P2)
open VerifiableInference.Desc.K2.Honest (K2Keeps k2Keeps_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h

/-- At number 339, in the output head's segment. -/
theorem k2_head_head :
    ∀ blk, cF.blocksInOrder[339]? = some blk → ∀ s s', StepYes 0 blk s s' →
      ∃ q : P2, q.stands = .head ∧ K2Keeps q s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, hx, hla, his⟩ := IM.k2_head_of h.scope h.reads O
  have hb1 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by decide) 1] at hb1
  have hb2 : cF.blocksInOrder[339]? = some b := hb1
  obtain rfl : b = blk := Option.some.inj (hb2.symm.trans hb)
  have hp := P1K2.flat_planOk O h.laid.planOk b (List.mem_of_getElem? hb)
  rw [IM.alone_planOk hla] at hp
  have hyp : y.planOk = true := (IM.retype_planOk y hp).1
  have hpl := P1K2.place_of_is his hyp
  obtain ⟨Q, n, -, -, e, arms⟩ := VerifiableInference.Desc.First.K2Caller.seated_is_pAt O.blank
    (H2K12.spots_atAll h (OnBytes.Road.K4.cut_of_head h.toAtMg)) hx hyp
  have hst : (ProofFile.pAtK2 Zp (n.grp - 1)).stands = .head := by
    rw [e, hpl, P1K2.links25_atAll h]
    rfl
  rcases arms with ⟨h0, -⟩ | ⟨-, l', HP, -, -, hy'⟩ | ⟨h0, -⟩
  · rw [hst] at h0
    cases h0
  · refine ⟨_, hst, k2Keeps_head hst y.name y.place HP (fun s rs gs t d => ?_) hy⟩
    obtain ⟨d1, hm⟩ := IM.alone_noMark hla d
    have d2 : y.decide s rs gs = .ok t := d1
    rw [hy'] at d2
    exact ⟨d2, hm⟩
  · rw [hst] at h0
    cases h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k2_head_head
