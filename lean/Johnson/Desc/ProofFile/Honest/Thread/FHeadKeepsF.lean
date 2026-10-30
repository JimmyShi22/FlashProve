-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsF.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for the sub-protocols of
the kind K1 that stand after a segment's first: the sendings of the reads and of the digits. 50 of
the 358 numbers. At these the arm of `fHead` is `K1KeepsAt` and `K1LaterRels`. The first comes from
`k1_member_later` (Johnson/Desc/ProofFile/Honest/K1/Law/KeepsMember.lean) of the authors of that
kind, the second from `rels_at_head` (K1LaterRelsHead.lean). Both speak of the sub-protocol at index
`i` of segment `l`. The library's `IM.hear_at_flat` and `IM.flatIx_scope` say that it stands at
number `14 * l + i + 2`. The lemma has the form that `head_hK_of_families` (SteppedYes.lean) takes.
No definition.

  1  `fHead_keeps_k1`   the lemma

Limits.
  * No hypothesis beside the library's `AtMgA`, the range of the segment's number, and that the list
    `kindsBeforeBatching` has K1 at the index. That a `StepYes` exists at any state is not shown.
  * Numbers 2 and 356, where K1's text is the first half of a sub-protocol, are not treated.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.Thread.K1LaterRelsHead
import Johnson.IMR.FlatScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At a sending of the kind K1 after a segment's first sub-protocol. -/
theorem fHead_keeps_k1 {l i : Nat} (hl : l < 25)
    (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some KindName.K1)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∀ blk, cF.blocksInOrder[14 * l + i + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hix : IM.flatIx cF l i = 14 * l + i + 2 :=
    IM.flatIx_scope h.scope h.reads O (by omega) i
  -- the kind's own clause
  obtain ⟨Lk, b, e1, e2, hK⟩ := ProofFile.Honest.K1.k1_member_later O l (IM.subAt l)
    (IM.subs_scope h.scope h.reads O l hl) i hk hi
  have hb1 := IM.hear_at_flat e1 e2
  rw [hix] at hb1
  obtain rfl : b = blk := Option.some.inj (hb1.symm.trans hb)
  -- the six relations
  obtain ⟨Lk', b', e1', e2', hR⟩ := rels_at_head h.toAtMg hl hk hi
  have hb2 := IM.hear_at_flat e1' e2'
  rw [hix] at hb2
  obtain rfl : b' = b := Option.some.inj (hb2.symm.trans hb)
  rw [head_place_hear h hl hk hb]
  exact (fHead_K1_later Zp cF G take P11 p12 P13
    (p := { chain := 1, link := some l, piece := i + 1, kind := .K1 }) (l := l) rfl
    (by show i + 1 ≠ 1; omega) s s').2 ⟨hK 0 s s' hy, hR 0 s s' hy⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k1
