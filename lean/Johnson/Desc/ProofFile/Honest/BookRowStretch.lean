-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookRowStretch.lean: what a sub-protocol of a segment spends is one
stretch of the segment's mask row, in the whole book of coins (`bookWhole`, Honest/BookWhole.lean).
Statements with their proofs. No definition.

  1  `spendingBook_open`   where `spendingBook` returns: the index-mask message as an owner, by
     `ownerOf`'s own term; the segments' and lone sums' stretches by their makers' own terms; that
     `wantsFree`
     accepts them; and of which five lists its entries are made
  2  `pick_whole`   of the whole book's entries those that a part of such a sub-protocol spends are
     among the segments' and lone sums' stretches
  3  `bookWhole_row_stretch`   WHERE `bookWhole` RETURNS B: `oneStretch` (Honest/BookStretch.lean)
     at the sub-protocol's row of parts: the owner, the first coin and the count

WHERE A CALLER GETS `hp : F.placesOk = true`. NOT from a return of `bookWhole` or `onlineProverFromPublicFiles`: neither
asks it. It is one of the tests in the description's own test on its plan (`FileDescription.planOkCore`, in
`FileDescription.planOk`: Johnson/Desc/Block.lean): whoever holds `F.planOk = true` has it.

Limits.
  * That `bookWhole` returns is a premise.
  * Of a sub-protocol one of whose parts is listed in `M.ends` (the parts that lay their end values
    under the index-mask message), or which holds a fold, or none of whose parts has a scalar of its
    own, nothing is said.
  * Nothing is evaluated: no number is written out at any public file.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRowKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

variable {Xi : Type}

theorem spendingBook_open {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B₀ : ProverCoinCounts} (h : spendingBook F p0 p1 p2 M = .ok B₀) :
    ∃ (idx : MsgAt) (a : List Want × Nat) (f0 f1 f2 : List Ahead),
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx M.ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      wantsFree (a.1 ++ (loneWants idx M.lone
          ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1) = true ∧
      foldEntries (planOf F.first.blocksInOrder) (planOf F.second.blocksInOrder) p0 = .ok f0 ∧
      foldEntries (planOf F.shared.blocksInOrder) [] p1 = .ok f1 ∧
      foldEntries (planOf F.second.blocksInOrder) [] p2 = .ok f2 ∧
      B₀.ahead = (a.1 ++ (loneWants idx M.lone
          ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).map
            (·.entry) ++ f0 ++ f1 ++ f2 ++ (splitEntry F.shared.blocksInOrder p1).toList := by
  unfold spendingBook at h
  obtain ⟨r0, -, h⟩ := ex_bind h
  obtain ⟨r1, -, h⟩ := ex_bind h
  obtain ⟨r2, -, h⟩ := ex_bind h
  rcases hidx : ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
      "link 0, moment 0" isIndexMaskMsg with _ | idx
  · rw [hidx] at h
    obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  rw [hidx] at h
  obtain ⟨idx', hy, h⟩ := ex_bind h
  obtain rfl : idx = idx' := Except.ok.inj hy
  obtain ⟨a, ha, h⟩ := ex_bind h
  rcases ex_ite h with ⟨-, h⟩ | ⟨hw, h⟩
  · obtain ⟨_, hc, -⟩ := ex_bind h
    exact absurd hc throw_ne
  have hfree : wantsFree (a.1 ++ (loneWants idx M.lone
      ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1) = true := by
    cases hq : wantsFree (a.1 ++ (loneWants idx M.lone
        ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1) with
    | true => rfl
    | false =>
      have hw' : ¬ (!wantsFree (a.1 ++ (loneWants idx M.lone
          ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1)) =
            true := hw
      rw [hq] at hw'
      exact absurd rfl hw'
  obtain ⟨_, -, h⟩ := ex_bind h
  obtain ⟨f0, hf0, h⟩ := ex_bind h
  obtain ⟨f1, hf1, h⟩ := ex_bind h
  obtain ⟨f2, hf2, h⟩ := ex_bind h
  have e := Except.ok.inj h
  exact ⟨idx, a, f0, f1, f2, hidx, ha, hfree, hf0, hf1, hf2, by subst e; rfl⟩

/-- At a sub-protocol of the first chain that holds no fold: of the whole book's entries those that
one of its parts spends are the segments' and lone sums' stretches that name that part. -/
theorem pick_whole {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
    (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∃ (idx : MsgAt) (a : List Want × Nat),
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx M.ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      wantsFree (a.1 ++ (loneWants idx M.lone
          ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1) = true ∧
      ∀ j, BookRow.pick ⟨b.place, j⟩ B.ahead =
        ((a.1 ++ (loneWants idx M.lone
          ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1).filter
            fun w => w.spender == ⟨b.place, j⟩).map (·.entry) := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := ex_bindE h
  obtain rfl := checked_ok hc
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, eW⟩ := bookRaw_ahead hW
  obtain ⟨idx, a, f0, f1, f2, hidx, ha, hfree, hf0, hf1, hf2, eB⟩ := spendingBook_open hB
  refine ⟨idx, a, hidx, ha, hfree, fun j => ?_⟩
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  have c1 : b.place.chain = 1 := chain_first hp _ (List.mem_map.2 ⟨b, hb, rfl⟩)
  -- no sub-protocol at b's place holds a fold
  have free1 : ∀ x ∈ planOf F.first.blocksInOrder, x.place = b.place →
      ∀ d ∈ x.rounds, d.entry.name ≠ "FOLD epsilon" := by
    intro x hx hpl
    unfold planOf at hx
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hx
    have e : b' = b := List.inj_on_of_nodup_map hn hb' hb hpl
    rw [e]
    exact hF
  have not2 : ∀ x ∈ planOf F.shared.blocksInOrder, x.place ≠ b.place := by
    intro x hx hpl
    have h2 := chain_shared hp x.place (by
      rw [← planOf_places]
      exact List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hpl] at h2
    omega
  have not3 : ∀ x ∈ planOf F.second.blocksInOrder, x.place ≠ b.place := by
    intro x hx hpl
    have h2 := chain_second hp x.place (by
      rw [← planOf_places]
      exact List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [hpl] at h2
    omega
  have z0 : BookRow.pick ⟨b.place, j⟩ f0 = [] := pick_other (by
    intro e he h0
    obtain ⟨x, hx, hx1, d, hd, hn0⟩ := foldEntries_spender hf0 e he
    rw [h0] at hx1
    rcases List.mem_append.1 hx with h1 | h1
    · exact free1 x h1 hx1 d hd hn0
    · exact not3 x h1 hx1)
  have z1 : BookRow.pick ⟨b.place, j⟩ f1 = [] := pick_other (by
    intro e he h0
    obtain ⟨x, hx, hx1, -⟩ := foldEntries_spender hf1 e he
    rw [h0] at hx1
    rcases List.mem_append.1 hx with h1 | h1
    · exact not2 x h1 hx1
    · cases h1)
  have z2 : BookRow.pick ⟨b.place, j⟩ f2 = [] := pick_other (by
    intro e he h0
    obtain ⟨x, hx, hx1, -⟩ := foldEntries_spender hf2 e he
    rw [h0] at hx1
    rcases List.mem_append.1 hx with h1 | h1
    · exact not3 x h1 hx1
    · cases h1)
  have z3 : BookRow.pick ⟨b.place, j⟩ (splitEntry F.shared.blocksInOrder p1).toList = [] := pick_other (by
             intro e he h0
             have hs : splitEntry F.shared.blocksInOrder p1 = some e := by
               cases hsp : splitEntry F.shared.blocksInOrder p1 with
               | none =>
                 rw [hsp] at he
                 cases he
               | some e' =>
                 rw [hsp] at he
                 rw [mem_one he]
             have h2 := chain_shared hp _ (splitEntry_spender hs)
             rw [h0] at h2
             have h3 : b.place.chain = 2 := h2
             omega)
  have z4 : BookRow.pick ⟨b.place, j⟩ seg = [] := pick_carried (segmentCarries_once hseg)
  have z5 : BookRow.pick ⟨b.place, j⟩ cF = [] := pick_carried (groupCarries_once hcF)
  have z6 : BookRow.pick ⟨b.place, j⟩ cO = [] := pick_carried (groupCarries_once hcO)
  have z7 : BookRow.pick ⟨b.place, j⟩ (carryPair pq.1 pq.2
      (m0.filter (·.masks) ++ (under m0 "W").filter (!·.fresh) ++
        (under m1 "Omega").filter (!·.masks))
      ((under m0 "W").find? (·.fresh))) = [] := pick_carried carryPair_once
  have z8 : BookRow.pick ⟨b.place, j⟩ ((ownFreshIn F.shared.blocksInOrder).map (·.carry tail)) = [] :=
    pick_carried (by
      intro e he
      obtain ⟨o, -, rfl⟩ := List.mem_map.1 he
      rfl)
  rw [eW, eB]
  simp only [pick_append]
  rw [z0, z1, z2, z3, z4, z5, z6, z7, z8, pick_entries]
  simp only [List.append_nil]

/-- **WHAT A SUB-PROTOCOL OF A SEGMENT SPENDS IS ONE STRETCH OF THE SEGMENT's MASK ROW**, in the
whole book: where none of its parts is listed in `M.ends` (the parts that lay their end values under
the index-mask message), it holds no fold, and it has a scalar of its own.
The owner: the mask row's sender. The first coin: where the
row's entries begin, and as many further as the segment's parts in front have scalars of their own.
The count: its own. OF A SUB-PROTOCOL NONE OF WHOSE PARTS HAS A SCALAR OF ITS OWN IT SAYS NOTHING:
such a one has no entry there, and `oneStretch [] = none`. -/
theorem bookWhole_row_stretch {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    (hM : ∀ p ∈ planParts b, p.addr ∉ M.ends)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon")
    (hs : ownScalarsOf (planParts b) ≠ 0) :
    ∃ row, ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      oneStretch (rowEntries B b.place (planParts b).length 0) =
        some (row.owner, row.base.e + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place),
          ownScalarsOf (planParts b)) := by
  obtain ⟨idx, a, -, ha, -, hpick⟩ := pick_whole h hp hb hF
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  obtain ⟨row, t', hrow, hat⟩ := linksWants_at _ 0 a (nodup_eraseDups _ _ (Nat.le_refl _))
    (List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨b, hb, hl⟩)) ha
  refine ⟨row, hrow, ?_⟩
  -- the segment's list of sub-protocols, cut at b
  obtain ⟨tl, ecut, hfront, hback⟩ := cut_at
    (F.first.blocksInOrder.filter fun x => x.place.link == some l)
    (nodup_filter_map _ _ _ hn)
    (List.mem_filter.2 ⟨hb, by rw [hl]; exact beq_self_eq_true _⟩)
  have eparts : (F.first.blocksInOrder.filter fun x => x.place.link == some l).flatMap planParts =
      partsInFront F.first.blocksInOrder l b.place ++ (planParts b ++ tl.flatMap planParts) := by
    unfold partsInFront
    conv_lhs => rw [ecut]
    rw [List.flatMap_append, List.flatMap_cons]
  -- b's own stretches
  have key : ∃ t2, ∀ j, BookRow.pick ⟨b.place, j⟩ B.ahead = BookRow.pick ⟨b.place, j⟩
      ((partsWants row idx M.ends (planParts b)
        (0 + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) t2).1.map (·.entry)) := by
    refine ⟨(partsWants row idx M.ends (partsInFront F.first.blocksInOrder l b.place) 0 t').2, fun j => ?_⟩
    have w0 : ((loneWants idx M.lone
        ((F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts) a.2).1.filter
          fun w => w.spender == (⟨b.place, j⟩ : Addr)) = [] := wants_other (by
      intro w hw h0
      obtain ⟨q, hq, e⟩ := loneWants_spender _ _ _ _ w hw
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      have h1 : x.place.link.isNone = true := (List.mem_filter.1 hx).2
      have h2 : x.place = b.place := by
        rw [← planParts_place hq2, ← e, h0]
      rw [h2, hl] at h1
      cases h1)
    have w1 : ((partsWants row idx M.ends (partsInFront F.first.blocksInOrder l b.place) 0 t').1.filter
        fun w => w.spender == (⟨b.place, j⟩ : Addr)) = [] := wants_other (by
      intro w hw h0
      obtain ⟨q, hq, e⟩ := partsWants_spender _ _ _ _ _ _ w hw
      unfold partsInFront at hq
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      exact hfront x hx (by rw [← planParts_place hq2, ← e, h0]))
    have w2 : ∀ j' t'', ((partsWants row idx M.ends (tl.flatMap planParts) j' t'').1.filter
        fun w => w.spender == (⟨b.place, j⟩ : Addr)) = [] := fun j' t'' => wants_other (by
      intro w hw h0
      obtain ⟨q, hq, e⟩ := partsWants_spender _ _ _ _ _ _ w hw
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      exact hback x hx (by rw [← planParts_place hq2, ← e, h0]))
    rw [hpick j, pick_entries, List.filter_append, hat ⟨b.place, j⟩ hl, w0, List.append_nil]
    unfold segmentWants
    rw [eparts, partsWants_append, partsWants_append, List.filter_append, List.filter_append,
      w1, List.nil_append, w2, List.append_nil]
  obtain ⟨t2, hkey⟩ := key
  rw [rowEntries_eq, rowPick_congr _ 0 (fun j _ => hkey j)]
  have hrow2 := rowPick_parts row idx M.ends b.place
    (stretchesBy (b.rounds.map fun r => (r.entry.name, scalarsIn r)) (partsCut b)) 0
    (0 + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) t2
  have hrow3 : rowPick ((partsWants row idx M.ends (planParts b)
      (0 + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) t2).1.map (·.entry)) b.place
      (planParts b).length 0 = (partsWants row idx M.ends (planParts b)
      (0 + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) t2).1.map (·.entry) := hrow2
  rw [hrow3]
  have hrun := runOn_parts row idx M.ends (planParts b)
    (0 + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) t2
    (row.base.e + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) 0
    (fun q hq => Bool.eq_false_iff.2 fun h0 => hM q hq (List.contains_iff_mem.1 h0))
    (by omega)
  rw [Nat.zero_add (ownScalarsOf (planParts b))] at hrun
  exact oneStretch_of_runOn hrun hs

end ProofFile.Honest

#print axioms ProofFile.Honest.spendingBook_open
#print axioms ProofFile.Honest.pick_whole
#print axioms ProofFile.Honest.bookWhole_row_stretch
