-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLoneStretch.lean: what a sub-protocol of the first chain that is
in no link spends is one block of the index-mask message, in the whole book of coins (`bookWhole`,
Honest/BookWhole.lean). The counterpart of `bookWhole_row_stretch` (Honest/BookRowStretch.lean),
which is about the sub-protocols of a link. Two definitions with code; lemmas with their proofs.

  `loneScalarsOf`   the scalars of those parts of a list that are masked sumchecks and are listed in
     `Merges.lone`, added up
  `lonePartsInFront`   the parts of the sub-protocols without a link that come before a place, in
     the chain's order: the counterpart of `partsInFront`
  `bookWhole_lone_stretch`   where `bookWhole` returns B: `oneStretch` (Honest/BookStretch.lean) at
     the sub-protocol's row of parts: the owner, the first coin and the count
  In the namespace `BookRow`, the lemmas under it: `loneStep`, `loneWants_next`,
     `loneWants_append`, `runOn_lone`, `rowPick_lone`, `linksWants_linked`

What the maker does (`loneWants`, Honest/BookAll.lean). It goes through the parts of the
sub-protocols without a link, in the chain's order, from the index-mask message's next free entry
after the links. A part that is listed in `Merges.lone`, is a masked sumcheck and has a scalar of
its own spends one block of that message: from the free entry on, as many coins as it has scalars of
its own. Every other part spends nothing there.

Limits.
  * That `bookWhole` returns, and the library's test `FileDescription.placesOk`, are hypotheses.
  * The number a.2, the index-mask message's next free entry after the links, is `linksWants`' own
    second component: what it is as a number computed from the plan is not stated here.
  * Nothing is said of a sub-protocol that contains a fold, or none of whose parts is such a
    sumcheck with a scalar of its own.
  * Nothing is evaluated: no number is written out at any public file.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookRowStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi S Cl : Type}

/-! ## 0 The definitions -/

/-- The scalars of those parts of a list that are masked sumchecks and are listed in `lone`, added
up. -/
def loneScalarsOf (lone : List Addr) (ps : List PartAt) : Nat :=
  ps.foldl (fun n p => if lone.contains p.addr && p.isSum then n + p.ownScalars else n) 0

/-- The parts of the sub-protocols without a link that come before a place, in the chain's order. -/
def lonePartsInFront (bs : List (Block S Cl)) (a : Place) : List PartAt :=
  ((bs.filter fun b => b.place.link.isNone).takeWhile fun b => b.place != a).flatMap planParts

namespace BookRow
open ProofFile.Honest.BookShared

/-! ## 1 Sums -/

theorem foldl_lone (lone : List Addr) (ps : List PartAt) : ∀ a,
    ps.foldl (fun n p => if lone.contains p.addr && p.isSum then n + p.ownScalars else n) a =
      a + loneScalarsOf lone ps := by
  induction ps with
  | nil => intro a; rfl
  | cons q ps ih =>
    intro a
    show List.foldl (fun n p => if lone.contains p.addr && p.isSum then n + p.ownScalars else n) a
        (q :: ps) =
      a + List.foldl (fun n p => if lone.contains p.addr && p.isSum then n + p.ownScalars else n) 0
        (q :: ps)
    rw [List.foldl_cons, List.foldl_cons, ih, ih]
    by_cases hc : (lone.contains q.addr && q.isSum) = true
    · rw [if_pos hc, if_pos hc]
      omega
    · rw [if_neg hc, if_neg hc]
      omega

theorem loneScalarsOf_cons (lone : List Addr) (q : PartAt) (ps : List PartAt) :
    loneScalarsOf lone (q :: ps) =
      (if lone.contains q.addr && q.isSum then q.ownScalars else 0) + loneScalarsOf lone ps := by
  show List.foldl (fun n p => if lone.contains p.addr && p.isSum then n + p.ownScalars else n) 0
      (q :: ps) = _
  rw [List.foldl_cons, foldl_lone]
  by_cases hc : (lone.contains q.addr && q.isSum) = true
  · rw [if_pos hc, if_pos hc]
    omega
  · rw [if_neg hc, if_neg hc]

/-! ## 2 One part's step -/

/-- One part's step of `loneWants`: nothing, and the part counts 0; or one block from t on, as long
as the part has scalars of its own. -/
theorem loneStep (idx : MsgAt) (lone : List Addr) (q : PartAt) (t : Nat) :
    ((if lone.contains q.addr then loneSumWants idx q t else ([], t)) = ([], t) ∧
        (if lone.contains q.addr && q.isSum then q.ownScalars else 0) = 0) ∨
      ((if lone.contains q.addr then loneSumWants idx q t else ([], t)) =
          ([⟨q.addr, "sum", idx, t, q.ownScalars⟩], t + q.ownScalars) ∧
        (if lone.contains q.addr && q.isSum then q.ownScalars else 0) = q.ownScalars) := by
  by_cases h1 : lone.contains q.addr = true
  · by_cases h2 : q.isSum = true
    · have hb : (lone.contains q.addr && q.isSum) = true := by
        rw [Bool.and_eq_true]
        exact ⟨h1, h2⟩
      by_cases h3 : q.ownScalars = 0
      · left
        have hc : ¬ (q.isSum && q.ownScalars != 0) = true := by
          intro hh
          rw [Bool.and_eq_true] at hh
          exact (bne_iff_ne.1 hh.2) h3
        refine ⟨?_, ?_⟩
        · rw [if_pos h1]
          unfold loneSumWants
          rw [if_neg hc]
        · rw [if_pos hb, h3]
      · right
        have hc : (q.isSum && q.ownScalars != 0) = true := by
          rw [h2, Bool.true_and]
          exact bne_iff_ne.2 h3
        refine ⟨?_, ?_⟩
        · rw [if_pos h1]
          unfold loneSumWants
          rw [if_pos hc]
        · rw [if_pos hb]
    · left
      have hb : ¬ (lone.contains q.addr && q.isSum) = true := by
        intro hh
        rw [Bool.and_eq_true] at hh
        exact h2 hh.2
      have hc : ¬ (q.isSum && q.ownScalars != 0) = true := by
        intro hh
        rw [Bool.and_eq_true] at hh
        exact h2 hh.1
      refine ⟨?_, ?_⟩
      · rw [if_pos h1]
        unfold loneSumWants
        rw [if_neg hc]
      · rw [if_neg hb]
  · left
    have hb : ¬ (lone.contains q.addr && q.isSum) = true := by
      intro hh
      rw [Bool.and_eq_true] at hh
      exact h1 hh.1
    exact ⟨by rw [if_neg h1], by rw [if_neg hb]⟩

theorem loneStep_spender (idx : MsgAt) (lone : List Addr) (q : PartAt) (t : Nat) :
    ∀ w ∈ (if lone.contains q.addr then loneSumWants idx q t else ([], t)).1,
      w.spender = q.addr := by
  intro w hw
  rcases loneStep idx lone q t with ⟨e, -⟩ | ⟨e, -⟩
  · rw [e] at hw
    try dsimp only at hw
    cases hw
  · rw [e] at hw
    try dsimp only at hw
    rw [mem_one hw]

/-! ## 3 The walk -/

/-- The next free entry behind a list of parts. -/
theorem loneWants_next (idx : MsgAt) (lone : List Addr) : ∀ (ps : List PartAt) (t : Nat),
    (loneWants idx lone ps t).2 = t + loneScalarsOf lone ps
  | [], _ => rfl
  | q :: ps, t => by
    rw [loneWants]
    dsimp only
    rw [loneWants_next idx lone ps, loneScalarsOf_cons]
    rcases loneStep idx lone q t with ⟨e, o⟩ | ⟨e, o⟩
    · rw [e, o]
      show t + loneScalarsOf lone ps = t + (0 + loneScalarsOf lone ps)
      omega
    · rw [e, o]
      show t + q.ownScalars + loneScalarsOf lone ps = t + (q.ownScalars + loneScalarsOf lone ps)
      omega

theorem loneWants_append (idx : MsgAt) (lone : List Addr) (C : List PartAt) :
    ∀ (A : List PartAt) (t : Nat),
      (loneWants idx lone (A ++ C) t).1 =
        (loneWants idx lone A t).1 ++ (loneWants idx lone C (loneWants idx lone A t).2).1
  | [], _ => rfl
  | q :: A, t => by
    rw [List.cons_append, loneWants, loneWants]
    dsimp only
    rw [loneWants_append idx lone C A, List.append_assoc]

/-- The blocks of a list of parts stand in a row. -/
theorem runOn_lone (idx : MsgAt) (lone : List Addr) :
    ∀ (ps : List PartAt) (t s c : Nat), s + c = idx.base.e + t →
      runOn idx.owner s c ((loneWants idx lone ps t).1.map (·.entry)) =
        some (c + loneScalarsOf lone ps)
  | [], _, _, _, _ => rfl
  | q :: ps, t, s, c, h => by
    rw [loneWants]
    dsimp only
    rw [loneScalarsOf_cons]
    rcases loneStep idx lone q t with ⟨e, o⟩ | ⟨e, o⟩
    · rw [e, o]
      show runOn idx.owner s c ((loneWants idx lone ps t).1.map (·.entry)) = _
      rw [runOn_lone idx lone ps t s c h]
      congr 1
      omega
    · rw [e, o]
      show runOn idx.owner s c ((⟨q.addr, "sum", idx, t, q.ownScalars⟩ : Want).entry ::
        (loneWants idx lone ps (t + q.ownScalars)).1.map (·.entry)) = _
      rw [runOn_one idx _ _ s c t _ h,
        runOn_lone idx lone ps (t + q.ownScalars) s (c + q.ownScalars) (by omega)]
      congr 1
      omega

/-- **The blocks of a row of parts, taken part by part, are the list itself.** -/
theorem rowPick_lone (idx : MsgAt) (lone : List Addr) (p : Place) :
    ∀ (L : List (List (String × Nat))) (k t : Nat),
      rowPick ((loneWants idx lone
          ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)) t).1.map (·.entry)) p
        ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)).length k =
      (loneWants idx lone
          ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)) t).1.map (·.entry)
  | [], _, _ => rfl
  | r :: L, k, t => by
    rw [List.zipIdx_cons, List.map_cons, List.length_cons, loneWants]
    dsimp only
    have hx : ∀ w ∈ (if lone.contains ⟨p, k⟩ then loneSumWants idx ⟨⟨p, k⟩, r⟩ t else ([], t)).1,
        w.spender = ⟨p, k⟩ := loneStep_spender idx lone ⟨⟨p, k⟩, r⟩ t
    have hy : ∀ w ∈ (loneWants idx lone
        ((L.zipIdx (k + 1)).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt))
        (if lone.contains ⟨p, k⟩ then loneSumWants idx ⟨⟨p, k⟩, r⟩ t else ([], t)).2).1,
        ∃ i, k + 1 ≤ i ∧ w.spender = ⟨p, i⟩ := by
      intro w hw
      obtain ⟨q, hq, e⟩ := loneWants_spender _ _ _ _ w hw
      obtain ⟨i, hi, e2⟩ := numbered_from p L (k + 1) q hq
      exact ⟨i, hi, e.trans e2⟩
    show pick ⟨p, k⟩ _ ++ rowPick _ p _ (k + 1) = _
    rw [List.map_append, pick_append, pick_entries, pick_entries, wants_all hx,
      wants_other (by
        intro w hw
        obtain ⟨i, hi, e⟩ := hy w hw
        rw [e]
        intro h0
        have h1 : i = k := congrArg Addr.part h0
        omega),
      List.map_nil, List.append_nil,
      rowPick_congr _ (k + 1) (l' := (loneWants idx lone
        ((L.zipIdx (k + 1)).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt))
        (if lone.contains ⟨p, k⟩ then loneSumWants idx ⟨⟨p, k⟩, r⟩ t else ([], t)).2).1.map
          (·.entry))
        (by
          intro i hi
          rw [pick_append, pick_entries, wants_other (by
            intro w hw
            rw [hx w hw]
            intro h0
            have h1 : k = i := congrArg Addr.part h0
            omega)]
          rfl),
      rowPick_lone idx lone p L (k + 1)]

/-! ## 4 The links' blocks are spent in links -/

theorem linksWants_linked {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok r →
      ∀ w ∈ r.1, ∃ l, w.spender.place.link = some l
  | [], t, r, h, w, hw => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l' :: ls, t, r, h, w, hw => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e] at hw
      rcases List.mem_append.1 hw with h1 | h1
      · exact ⟨l', segmentWants_link bs l' row idx merges t w h1⟩
      · exact linksWants_linked ls _ y hy w h1

end BookRow

open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

/-! ## 5 The statement -/

/-- **WHAT A SUB-PROTOCOL WITHOUT A LINK SPENDS IS ONE BLOCK OF THE INDEX-MASK MESSAGE.** Where
`bookWhole` returns B, at a sub-protocol of the first chain that is in no link, contains no fold,
and has a masked sumcheck listed in `Merges.lone` with a scalar of its own. The owner: the
index-mask message's sender. The first coin: where that message's entries begin, then the entries
that the links have taken (a.2), then as many as the listed sumchecks before it have scalars of
their own. The count: its own. It does not say what a.2 is as a number computed from the plan, nor
that `bookWhole` returns. -/
theorem bookWhole_lone_stretch {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) (hl : b.place.link = none)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon")
    (hs : loneScalarsOf M.lone (planParts b) ≠ 0) :
    ∃ (idx : MsgAt) (a : List Want × Nat),
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      linksWants F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) idx M.ends
        (F.first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 = .ok a ∧
      oneStretch (rowEntries B b.place (planParts b).length 0) =
        some (idx.owner,
          idx.base.e + (a.2 + loneScalarsOf M.lone (lonePartsInFront F.first.blocksInOrder b.place)),
          loneScalarsOf M.lone (planParts b)) := by
  obtain ⟨idx, a, hidx, ha, -, hpick⟩ := pick_whole h hp hb hF
  refine ⟨idx, a, hidx, ha, ?_⟩
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  -- the list of sub-protocols without a link, cut at b
  obtain ⟨tl, ecut, hfront, hback⟩ := cut_at
    (F.first.blocksInOrder.filter fun x => x.place.link.isNone)
    (nodup_filter_map _ _ _ hn)
    (List.mem_filter.2 ⟨hb, by simp [hl]⟩)
  have eparts : (F.first.blocksInOrder.filter fun x => x.place.link.isNone).flatMap planParts =
      lonePartsInFront F.first.blocksInOrder b.place ++ (planParts b ++ tl.flatMap planParts) := by
    unfold lonePartsInFront
    conv_lhs => rw [ecut]
    rw [List.flatMap_append, List.flatMap_cons]
  -- b's own blocks
  have key : ∀ j, BookRow.pick ⟨b.place, j⟩ B.ahead = BookRow.pick ⟨b.place, j⟩
      ((loneWants idx M.lone (planParts b)
        (loneWants idx M.lone (lonePartsInFront F.first.blocksInOrder b.place) a.2).2).1.map
          (·.entry)) := by
    intro j
    have w0 : (a.1.filter fun w => w.spender == (⟨b.place, j⟩ : Addr)) = [] := wants_other (by
      intro w hw h0
      obtain ⟨l, h1⟩ := linksWants_linked _ 0 a ha w hw
      rw [h0] at h1
      have h2 : b.place.link = some l := h1
      rw [hl] at h2
      cases h2)
    have w1 : ((loneWants idx M.lone (lonePartsInFront F.first.blocksInOrder b.place) a.2).1.filter
        fun w => w.spender == (⟨b.place, j⟩ : Addr)) = [] := wants_other (by
      intro w hw h0
      obtain ⟨q, hq, e⟩ := loneWants_spender _ _ _ _ w hw
      unfold lonePartsInFront at hq
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      exact hfront x hx (by rw [← planParts_place hq2, ← e, h0]))
    have w2 : ∀ t'', ((loneWants idx M.lone (tl.flatMap planParts) t'').1.filter
        fun w => w.spender == (⟨b.place, j⟩ : Addr)) = [] := fun t'' => wants_other (by
      intro w hw h0
      obtain ⟨q, hq, e⟩ := loneWants_spender _ _ _ _ w hw
      obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
      exact hback x hx (by rw [← planParts_place hq2, ← e, h0]))
    rw [hpick j, pick_entries, List.filter_append, w0, List.nil_append, eparts,
      loneWants_append, loneWants_append, List.filter_append, List.filter_append,
      w1, List.nil_append, w2, List.append_nil]
  rw [rowEntries_eq, rowPick_congr _ 0 (fun j _ => key j)]
  have hrow2 := rowPick_lone idx M.lone b.place
    (stretchesBy (b.rounds.map fun r => (r.entry.name, scalarsIn r)) (partsCut b)) 0
    (loneWants idx M.lone (lonePartsInFront F.first.blocksInOrder b.place) a.2).2
  have hrow3 : rowPick ((loneWants idx M.lone (planParts b)
      (loneWants idx M.lone (lonePartsInFront F.first.blocksInOrder b.place) a.2).2).1.map (·.entry))
      b.place (planParts b).length 0 = (loneWants idx M.lone (planParts b)
      (loneWants idx M.lone (lonePartsInFront F.first.blocksInOrder b.place) a.2).2).1.map (·.entry) :=
    hrow2
  rw [hrow3]
  have hrun := runOn_lone idx M.lone (planParts b)
    (loneWants idx M.lone (lonePartsInFront F.first.blocksInOrder b.place) a.2).2
    (idx.base.e + (a.2 + loneScalarsOf M.lone (lonePartsInFront F.first.blocksInOrder b.place))) 0
    (by rw [loneWants_next]; omega)
  rw [Nat.zero_add (loneScalarsOf M.lone (planParts b))] at hrun
  exact oneStretch_of_runOn hrun hs

end ProofFile.Honest

#print axioms ProofFile.Honest.BookRow.foldl_lone
#print axioms ProofFile.Honest.BookRow.loneScalarsOf_cons
#print axioms ProofFile.Honest.BookRow.loneStep
#print axioms ProofFile.Honest.BookRow.loneStep_spender
#print axioms ProofFile.Honest.BookRow.loneWants_next
#print axioms ProofFile.Honest.BookRow.loneWants_append
#print axioms ProofFile.Honest.BookRow.runOn_lone
#print axioms ProofFile.Honest.BookRow.rowPick_lone
#print axioms ProofFile.Honest.BookRow.linksWants_linked
#print axioms ProofFile.Honest.bookWhole_lone_stretch
