-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/K1LaterRelsHead.lean: the six relations `K1LaterRels`
(K1LaterRels.lean) at the first chain at the full size, under the library's hypothesis `AtMg`. The
relations are to become part of a clause of `keeps`, so it has to be possible to show them at the
sub-protocols at which that clause is asked. This file shows them there from an accepting step. No
definition.

  1  `rels_at_head`   at every segment `l` below 25 and every index `i` after the first at which the
     list of kinds of segment `l` has K1: the chain has a sub-protocol there, and each of its
     accepting steps gives the six relations
  2  `rels_at_head_reads0`, `rels_at_head_digits0`   lemma 1 at two places: segment 0, indices 3 and
     5. They show that the hypotheses of lemma 1 on `l` and `i` can be met
  3  `rels_places_count`   the hypotheses of lemma 1 on `l` and `i` are met at 50 pairs

Limits.
  * Full size only, and only under the library's hypothesis `AtMg` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * One direction: from an accepting step. That a sub-protocol accepts anywhere is not shown.
  * The sub-protocol is named by its segment and its index in the segment's list, not by its number
    in the chain's flat list.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K1LaterRels
import Johnson.P5J.AtMg
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching)
open OnBytes.Maker (WholeD)
open P5J (AtMg TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- **At the first chain at the full size**: each accepting step of a sub-protocol of kind K1 after
a segment's first gives the six relations. -/
theorem rels_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l i : Nat} (hl : l < 25)
    (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some KindName.K1)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk b, cF.links[l]? = some Lk ∧ Lk.hear[i]? = some b ∧
      ∀ ft s s', StepYes ft b s s' → K1LaterRels s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact rels_member_later O l (IM.subAt l) (IM.subs_scope h.scope h.reads O l hl) i hk hi

/-- Lemma 1 at the reads of segment 0. -/
theorem rels_at_head_reads0 (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ Lk b, cF.links[0]? = some Lk ∧ Lk.hear[3]? = some b ∧
      ∀ ft s s', StepYes ft b s s' → K1LaterRels s s' :=
  rels_at_head h (by decide) (by decide) (by decide)

/-- Lemma 1 at the digits of segment 0. -/
theorem rels_at_head_digits0 (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ Lk b, cF.links[0]? = some Lk ∧ Lk.hear[5]? = some b ∧
      ∀ ft s s', StepYes ft b s s' → K1LaterRels s s' :=
  rels_at_head h (by decide) (by decide) (by decide)

/-- The hypotheses of lemma 1 on `l` and `i` are met at 50 pairs. -/
theorem rels_places_count :
    ((List.range 25).flatMap fun l => (List.range 9).filter fun i =>
      decide ((kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some KindName.K1) && decide (1 ≤ i)).length =
      50 := by decide

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rels_at_head
#print axioms ProofFile.Honest.FirstThread.rels_at_head_reads0
#print axioms ProofFile.Honest.FirstThread.rels_at_head_digits0
#print axioms ProofFile.Honest.FirstThread.rels_places_count
