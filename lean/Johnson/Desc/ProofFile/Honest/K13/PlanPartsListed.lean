-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PlanPartsListed.lean: kind K13, the members' batching: AT THE LIST
`mergesByName bs` (Honest/BookWhole.lean: the maker's guess which masked sumchecks are merges), AND
WHERE THE MAKER `bookWhole` RETURNS A BOOK AT THAT LIST: WHAT A SUB-PROTOCOL THAT HAS THE KIND's
ROUNDS AND STANDS AT THE KIND's PLACE SPENDS IS ONE STRETCH OF 2 kCol + 1 ENTRIES OF THE INDEX-MASK
MESSAGE, FROM THE ENTRY ON THAT THE LINKS LEAVE FREE. IT PAYS NO DEBT ON ANY BOOK BY ITSELF: THAT
`bookWhole` RETURNS IS A PREMISE. Statements with their proofs; no definition. General in the
description and in the kind's numbers: no hypothesis on a proof file, no closed fact.

Main names: `k13_listed_mergesByName`: the second part's address is in the list.
`mergesByName_lone_kind`: every address in the list stands at a place of the kind K13.
`k13_none_listed`: over the parts of sub-protocols none of which is of the kind K13, the listed
sumchecks' own scalars (`loneScalarsOf`, Honest/BookLoneStretch.lean) add up to 0.
`k13_lone_scalars`, `k13_lone_scalars_ne`: **at the kind's sub-protocol they add up to 2 kCol + 1**;
that is not 0. `k13_none_in_front`: where no sub-protocol without a link in front of a place is of
the kind K13, those in front (`lonePartsInFront`) add up to 0. `k13_stretch_of_whole`: **the join.**

Why. The frame's law `bookWhole_lone_stretch` (Honest/BookLoneStretch.lean) says what a sub-protocol
of the first chain that is in no link spends, in the maker's terms. The premise on the book in
CoinsTieAtHead.lean of this folder (hS) has written numbers. `k13_stretch_of_whole` is that law at
the kind's sub-protocol with its three premises on the sub-protocol paid and its three counts
written out: two parts; nothing in front; 2 kCol + 1.

How. PlanPartsAtM3.lean of this folder says what the maker reads off the plan at the kind's rounds.
The list `mergesByName` holds the addresses of the parts that are masked sumchecks at places of the
kind K13. That a part of a sub-protocol stands at that sub-protocol's place is the frame's
`BookRow.planParts_place` (Honest/BookRowKit.lean).

Limits. THAT `bookWhole` RETURNS, and that the description's places pass `placesOk`, are premises.
At `mergesByName` alone, the one list that a caller of the maker's hands it so far (`onlineProverFromPublicFiles`,
Honest/AtPure.lean); at another list, its maker's matter. The owner idx.owner, the message's first
entry idx.base.e and the number a.2 that the links leave stand in the end as the maker's own terms:
what they are as numbers off the plan is not said. hc (no sub-protocol without a link in front of
the place is of the kind K13) is a premise. Nothing outside this folder calls these statements. They
say what functions of the plan return: nothing on what an entry is for, or on what a part does.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.PlanPartsAtM3
import Johnson.Desc.ProofFile.Honest.BookLoneStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.K13 (Where battRounds)

variable {S Cl : Type}

/-- **AT THE MAKER's OWN GUESS `mergesByName` THE SUM's PART IS LISTED.** -/
theorem k13_listed_mergesByName {bs : List (Block S Cl)} {b : Block S Cl} {p : Where}
    (hb : b ∈ bs) (hr : b.rounds = battRounds p) (hp : b.place = k13Place p) :
    (mergesByName bs).lone.contains ⟨k13Place p, 1⟩ = true := by
  have hm : k13SumPartAt p ∈ bs.flatMap planParts :=
    List.mem_flatMap.2 ⟨b, hb, by rw [k13_planParts_of hr hp]; simp⟩
  have hf : k13SumPartAt p ∈ (bs.flatMap planParts).filter
      fun q => q.isSum && q.addr.place.kind == .K13 :=
    List.mem_filter.2 ⟨hm, by rw [k13_sumPart_isSum]; rfl⟩
  exact List.contains_iff_mem.2 (List.mem_map.2 ⟨_, hf, rfl⟩)

/-- Every address that `mergesByName` lists as lone stands at a place of the kind K13. -/
theorem mergesByName_lone_kind {bs : List (Block S Cl)} {a : Addr}
    (ha : a ∈ (mergesByName bs).lone) : a.place.kind = .K13 := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ha
  have h2 := (List.mem_filter.1 hq).2
  rw [Bool.and_eq_true] at h2
  exact eq_of_beq h2.2

/-- **NO LISTED SUMCHECK AMONG THE PARTS OF SUB-PROTOCOLS OF OTHER KINDS.** -/
theorem k13_none_listed {bs cs : List (Block S Cl)} (hc : ∀ c ∈ cs, c.place.kind ≠ .K13) :
    loneScalarsOf (mergesByName bs).lone (cs.flatMap planParts) = 0 := by
  have hq : ∀ q ∈ cs.flatMap planParts, (mergesByName bs).lone.contains q.addr = false := by
    intro q hm
    obtain ⟨c, hcm, hqc⟩ := List.mem_flatMap.1 hm
    cases e : (mergesByName bs).lone.contains q.addr with
    | false => rfl
    | true =>
      have hk := mergesByName_lone_kind (List.contains_iff_mem.1 e)
      rw [BookRow.planParts_place hqc] at hk
      exact absurd hk (hc c hcm)
  unfold loneScalarsOf
  generalize cs.flatMap planParts = l at hq
  induction l with
  | nil => rfl
  | cons q l ih =>
    rw [List.foldl_cons, hq q (List.mem_cons_self ..)]
    exact ih fun q' h' => hq q' (List.mem_cons_of_mem _ h')

/-- **AT THE KIND's SUB-PROTOCOL THE LISTED SUMCHECKS' OWN SCALARS ADD UP TO 2 kCol + 1.** -/
theorem k13_lone_scalars {bs : List (Block S Cl)} {b : Block S Cl} {p : Where}
    (hb : b ∈ bs) (hr : b.rounds = battRounds p) (hp : b.place = k13Place p) :
    loneScalarsOf (mergesByName bs).lone (planParts b) = 2 * p.lin.kCol + 1 :=
  k13_listed_scalars hr hp _ (k13_listed_mergesByName hb hr hp)

/-- That is not 0. -/
theorem k13_lone_scalars_ne {bs : List (Block S Cl)} {b : Block S Cl} {p : Where}
    (hb : b ∈ bs) (hr : b.rounds = battRounds p) (hp : b.place = k13Place p) :
    loneScalarsOf (mergesByName bs).lone (planParts b) ≠ 0 := by
  rw [k13_lone_scalars hb hr hp]
  omega

/-- **NOTHING IN FRONT**: where no sub-protocol without a link in front of the place is of the kind
K13. -/
theorem k13_none_in_front {bs : List (Block S Cl)} {a : Place}
    (hc : ∀ c ∈ (bs.filter fun x => x.place.link.isNone).takeWhile fun x => x.place != a,
      c.place.kind ≠ .K13) :
    loneScalarsOf (mergesByName bs).lone (lonePartsInFront bs a) = 0 :=
  k13_none_listed hc

/-- **THE JOIN, GENERAL IN THE DESCRIPTION AND IN THE KIND's NUMBERS**: the frame's
`bookWhole_lone_stretch` at a sub-protocol that has the kind's rounds at the kind's place, its
counts written out. THAT `bookWhole` RETURNS IS A PREMISE. idx and a are the maker's own terms: what
idx.owner, idx.base.e and a.2 are as numbers off the plan is not said. -/
theorem k13_stretch_of_whole {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends}
    {B : ProverCoinCounts} (hW : bookWhole F p0 p1 p2 (mergesByName F.first.blocksInOrder) = .ok B)
    (hpl : F.placesOk = true) {b : Block F.S₁ F.Cl} {p : Where} (hb : b ∈ F.first.blocksInOrder)
    (hr : b.rounds = battRounds p) (hp : b.place = k13Place p)
    (hc : ∀ c ∈ (F.first.blocksInOrder.filter fun x => x.place.link.isNone).takeWhile
      fun x => x.place != b.place, c.place.kind ≠ .K13) :
    ∃ (idx : MsgAt) (a : List Want × Nat),
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx
        (mergesByName F.first.blocksInOrder).ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      oneStretch (rowEntries B b.place 2 0) =
        some (idx.owner, idx.base.e + a.2, 2 * p.lin.kCol + 1) := by
  obtain ⟨idx, a, hi, ha, e⟩ := bookWhole_lone_stretch hW hpl hb (by rw [hp]; rfl)
    (k13_no_fold_epsilon hr) (k13_lone_scalars_ne hb hr hp)
  refine ⟨idx, a, hi, ha, ?_⟩
  rw [k13_planParts_length hr hp, k13_none_in_front hc, k13_lone_scalars hb hr hp,
    Nat.add_zero] at e
  exact e

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_listed_mergesByName
#print axioms ProofFile.Honest.K13.mergesByName_lone_kind
#print axioms ProofFile.Honest.K13.k13_none_listed
#print axioms ProofFile.Honest.K13.k13_lone_scalars
#print axioms ProofFile.Honest.K13.k13_lone_scalars_ne
#print axioms ProofFile.Honest.K13.k13_none_in_front
#print axioms ProofFile.Honest.K13.k13_stretch_of_whole
