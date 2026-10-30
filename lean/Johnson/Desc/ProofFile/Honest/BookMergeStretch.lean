-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookMergeStretch.lean: what a sub-protocol of a link spends, in the
whole book of coins (`bookWhole`, Honest/BookWhole.lean), whether or not one of its parts is a
merge. A merge is a masked sumcheck whose end values are masked by entries of the index-mask message
and not of its segment's mask row (`Merges.ends`, Honest/BookAll.lean). Two definitions with code;
lemmas with their proofs.

  `mergeEndsOf`   the end values of those parts of a list that are merges, added up
  `linksInFront`   the parts of the links that the maker goes through before the link number l
  `bookWhole_row_wants`   where `bookWhole` returns B: the spending entries of the sub-protocol's
     row of parts are the entries of `partsWants` (Honest/BookEntries.lean) at that row, from two
     numbers that are computed from the plan. No hypothesis on merges
  `bookWhole_merge_stretch`   at a row whose last spending part is a merge, and which spends at
     least one entry of the mask row: all entries but the last are one block of the mask row
     (`oneStretch`, Honest/BookStretch.lean); the last is the merge's entry of the index-mask
     message
  `linksWants_next`   the index-mask message's next free entry after the links
  In the namespace `BookRow`, the lemmas under them: `partWants_next`, `partsWants_next`,
     `linksWants_at_t`, `partsWants_merge`, `oneStretch_merge` and smaller ones

The two numbers. j: the number, in the mask row's own count, of the row's first scalar: the scalars
of the segment's parts in front of the row (`ownScalarsOf`, `partsInFront`, Honest/BookRowKit.lean).
t: the index-mask message's next free entry: the end values of the merges in front, first those of
the links that the maker goes through earlier, then those of this link's parts in front of the row.

After a merge the mask row has a gap. For a merge with s scalars of its own, n of them end values,
`partWants` makes one block of s - n entries of the mask row from j on, and one block of n entries
of the index-mask message. `partsWants` lets the next part begin at j + s. So the n entries of the
mask row from j + (s - n) on are spent by no part. If a part after the merge spends coins, the row's
entries of the mask row are not one block, and `oneStretch` returns `none` for them. That is why
`bookWhole_merge_stretch` asks that no part after the merge has a scalar of its own.

Related lemmas. `bookWhole_row_stretch` (Honest/BookRowStretch.lean) is the case of a row without a
merge; `bookWhole_lone_stretch` (Honest/BookLoneStretch.lean) is about sub-protocols in no link.
`linksWants_at_t` is `linksWants_at` (Honest/BookRowKit.lean) with the number t written out.

Limits.
  * That `bookWhole` returns, and that the description's test on its places passes
    (`F.placesOk`), are hypotheses.
  * Which parts are merges is the argument M. Nothing compares it with the format.
  * Nothing is said of a sub-protocol that contains a fold.
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

/-- The end values of those parts of a list that are merges, added up: of the parts that are listed
in `merges`, are masked sumchecks and have a scalar of their own. -/
def mergeEndsOf (merges : List Addr) (ps : List PartAt) : Nat :=
  ps.foldl (fun n p =>
    n + if merges.contains p.addr && p.isSum && p.ownScalars != 0 then p.endScalars else 0) 0

/-- The parts of the links that the maker goes through before the link number l, in its order. -/
def linksInFront (bs : List (Block S Cl)) (l : Nat) : List PartAt :=
  ((bs.filterMap (·.place.link)).eraseDups.takeWhile (· != l)).flatMap fun l' =>
    (bs.filter fun b => b.place.link == some l').flatMap planParts

namespace BookRow
open ProofFile.Honest.BookShared

/-! ## 1 Sums -/

theorem foldl_mergeEnds (merges : List Addr) (ps : List PartAt) : ∀ a,
    ps.foldl (fun n p =>
      n + if merges.contains p.addr && p.isSum && p.ownScalars != 0 then p.endScalars else 0) a =
      a + mergeEndsOf merges ps := by
  induction ps with
  | nil => intro a; rfl
  | cons q ps ih =>
    intro a
    show List.foldl (fun n p =>
        n + if merges.contains p.addr && p.isSum && p.ownScalars != 0 then p.endScalars else 0) a
        (q :: ps) =
      a + List.foldl (fun n p =>
        n + if merges.contains p.addr && p.isSum && p.ownScalars != 0 then p.endScalars else 0) 0
        (q :: ps)
    rw [List.foldl_cons, List.foldl_cons, ih, ih]
    omega

theorem mergeEndsOf_cons (merges : List Addr) (q : PartAt) (ps : List PartAt) :
    mergeEndsOf merges (q :: ps) =
      (if merges.contains q.addr && q.isSum && q.ownScalars != 0 then q.endScalars else 0) +
        mergeEndsOf merges ps := by
  show List.foldl (fun n p =>
      n + if merges.contains p.addr && p.isSum && p.ownScalars != 0 then p.endScalars else 0) 0
      (q :: ps) = _
  rw [List.foldl_cons, foldl_mergeEnds]
  omega

theorem mergeEndsOf_append (merges : List Addr) (C : List PartAt) : ∀ A : List PartAt,
    mergeEndsOf merges (A ++ C) = mergeEndsOf merges A + mergeEndsOf merges C
  | [] => by
    show mergeEndsOf merges C = 0 + mergeEndsOf merges C
    omega
  | q :: A => by
    rw [List.cons_append, mergeEndsOf_cons, mergeEndsOf_cons, mergeEndsOf_append merges C A]
    omega

/-- A list without a merge counts 0. -/
theorem mergeEndsOf_none {merges : List Addr} : ∀ {A : List PartAt},
    (∀ q ∈ A, merges.contains q.addr = false) → mergeEndsOf merges A = 0
  | [], _ => rfl
  | q :: A, h => by
    have hc : ¬ (merges.contains q.addr && q.isSum && q.ownScalars != 0) = true := by
      rw [h q (List.Mem.head _)]
      simp
    rw [mergeEndsOf_cons, if_neg hc, mergeEndsOf_none fun q' hq' => h q' (List.Mem.tail _ hq')]

/-! ## 2 The index-mask message's next free entry -/

/-- One part: the next free entry moves on by the part's end values if it is a merge. -/
theorem partWants_next (row idx : MsgAt) (merges : List Addr) (q : PartAt) (j t : Nat) :
    (partWants row idx (merges.contains q.addr) q j t).2 =
      t + if merges.contains q.addr && q.isSum && q.ownScalars != 0 then q.endScalars else 0 := by
  by_cases h0 : q.ownScalars = 0
  · have c0 : (q.ownScalars == 0) = true := beq_iff_eq.2 h0
    have cN : ¬ (merges.contains q.addr && q.isSum && q.ownScalars != 0) = true := by
      intro hh
      rw [Bool.and_eq_true] at hh
      exact (bne_iff_ne.1 hh.2) h0
    unfold partWants
    dsimp only
    rw [if_pos c0, if_neg cN]
    rfl
  · have c0 : ¬ (q.ownScalars == 0) = true := fun hh => h0 (beq_iff_eq.1 hh)
    by_cases h1 : q.isSum = true
    · have c1 : ¬ (!q.isSum) = true := by
        rw [h1]
        decide
      by_cases hn : q.endScalars = 0
      · have c2 : (q.endScalars == 0) = true := beq_iff_eq.2 hn
        unfold partWants
        dsimp only
        rw [if_neg c0, if_neg c1, if_pos c2, hn, ite_self]
        rfl
      · have c2 : ¬ (q.endScalars == 0) = true := fun hh => hn (beq_iff_eq.1 hh)
        by_cases hm : merges.contains q.addr = true
        · have cY : (merges.contains q.addr && q.isSum && q.ownScalars != 0) = true := by
            rw [hm, h1, Bool.true_and, Bool.true_and]
            exact bne_iff_ne.2 h0
          unfold partWants
          dsimp only
          rw [if_neg c0, if_neg c1, if_neg c2, if_pos hm, if_pos cY]
        · have cN : ¬ (merges.contains q.addr && q.isSum && q.ownScalars != 0) = true := by
            intro hh
            rw [Bool.and_eq_true, Bool.and_eq_true] at hh
            exact hm hh.1.1
          unfold partWants
          dsimp only
          rw [if_neg c0, if_neg c1, if_neg c2, if_neg hm, if_neg cN]
          rfl
    · have e1 : q.isSum = false := Bool.eq_false_iff.2 h1
      have c1 : (!q.isSum) = true := by
        rw [e1]
        rfl
      have cN : ¬ (merges.contains q.addr && q.isSum && q.ownScalars != 0) = true := by
        intro hh
        rw [Bool.and_eq_true, Bool.and_eq_true] at hh
        exact h1 hh.1.2
      unfold partWants
      dsimp only
      rw [if_neg c0, if_pos c1, if_neg cN]
      rfl

/-- Parts in a row. -/
theorem partsWants_next (row idx : MsgAt) (merges : List Addr) : ∀ (ps : List PartAt) (j t : Nat),
    (partsWants row idx merges ps j t).2 = t + mergeEndsOf merges ps
  | [], _, _ => rfl
  | q :: ps, j, t => by
    rw [partsWants]
    dsimp only
    rw [partsWants_next row idx merges ps, partWants_next, mergeEndsOf_cons]
    omega

/-- A segment. -/
theorem segmentWants_next (bs : List (Block S Cl)) (l : Nat) (row idx : MsgAt)
    (merges : List Addr) (t : Nat) :
    (segmentWants bs l row idx merges t).2 =
      t + mergeEndsOf merges ((bs.filter fun b => b.place.link == some l).flatMap planParts) := by
  unfold segmentWants
  exact partsWants_next row idx merges _ 0 t

end BookRow

open ProofFile.Honest.BookShared ProofFile.Honest.BookRow

/-- **The index-mask message's next free entry after the links**: the end values of all merges of
the links that are listed, added to the entry at which the maker began. -/
theorem linksWants_next {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat),
      linksWants bs c later idx merges ls t = .ok r →
      r.2 = t + mergeEndsOf merges (ls.flatMap fun l' =>
        (bs.filter fun b => b.place.link == some l').flatMap planParts)
  | [], t, r, h => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e]
    rfl
  | l' :: ls, t, r, h => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e]
      show y.2 = _
      rw [linksWants_next ls _ y hy, segmentWants_next, List.flatMap_cons, mergeEndsOf_append]
      omega

namespace BookRow

/-- **`linksWants_at` with the number written out**: of all segments' stretches those that are spent
in the segment number l are that segment's, made from the entry that the merges of the links in
front have reached. -/
theorem linksWants_at_t {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} {l : Nat} :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat), ls.Nodup → l ∈ ls →
      linksWants bs c later idx merges ls t = .ok r →
      ∃ row, ownerOf maskRowRun bs c later s!"link {l}, moment 0" isMaskRowMsg = some row ∧
        ∀ a : Addr, a.place.link = some l →
          r.1.filter (fun w => w.spender == a) =
            (segmentWants bs l row idx merges
              (t + mergeEndsOf merges ((ls.takeWhile (· != l)).flatMap fun l' =>
                (bs.filter fun b => b.place.link == some l').flatMap planParts))).1.filter
              fun w => w.spender == a
  | [], _, _, _, hl, _ => by cases hl
  | l' :: ls, t, r, hn, hl, h => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      obtain ⟨hn1, hn2⟩ := List.nodup_cons.1 hn
      by_cases hll : l' = l
      · subst hll
        refine ⟨row, hrow, fun a ha => ?_⟩
        have h0 : ¬ ((fun x : Nat => x != l') l' = true) := by simp
        rw [List.takeWhile_cons_of_neg (p := fun x : Nat => x != l') (a := l') h0]
        show _ = (segmentWants bs l' row idx merges t).1.filter fun w => w.spender == a
        rw [← e]
        show (_ ++ y.1).filter _ = _
        rw [List.filter_append, wants_other (ws := y.1) (by
          intro w hw h1
          exact linksWants_none ls _ y hn1 hy w hw (h1 ▸ ha)), List.append_nil]
      · have hl2 : l ∈ ls := by
          cases hl with
          | head => exact absurd rfl hll
          | tail _ h2 => exact h2
        obtain ⟨row2, hr2, hf2⟩ := linksWants_at_t ls _ y hn2 hl2 hy
        refine ⟨row2, hr2, fun a ha => ?_⟩
        have h0 : (fun x : Nat => x != l) l' = true := by simp [hll]
        have et : t + mergeEndsOf merges
              (((l' :: ls).takeWhile fun x : Nat => x != l).flatMap fun k =>
              (bs.filter fun b => b.place.link == some k).flatMap planParts) =
            (segmentWants bs l' row idx merges t).2 +
              mergeEndsOf merges ((ls.takeWhile fun x : Nat => x != l).flatMap fun k =>
                (bs.filter fun b => b.place.link == some k).flatMap planParts) := by
          rw [List.takeWhile_cons_of_pos (p := fun x : Nat => x != l) (a := l') h0,
            List.flatMap_cons, mergeEndsOf_append, segmentWants_next]
          omega
        rw [et, ← e]
        show (_ ++ y.1).filter _ = _
        rw [List.filter_append, wants_other (by
          intro w hw h1
          have h3 := segmentWants_link bs l' row idx merges t w hw
          rw [h1, ha] at h3
          exact hll (Option.some.inj h3).symm), List.nil_append]
        exact hf2 a ha

/-! ## 3 A row whose last spending part is a merge -/

/-- What `partWants` makes for a merge with an end value. -/
theorem partWants_merge (row idx : MsgAt) {merges : List Addr} {m : PartAt}
    (hm : merges.contains m.addr = true) (hS : m.isSum = true) (hN : m.endScalars ≠ 0)
    (j t : Nat) :
    partWants row idx (merges.contains m.addr) m j t =
      ([⟨m.addr, "sum", row, j, m.ownScalars - m.endScalars⟩,
        ⟨m.addr, "ends", idx, t, m.endScalars⟩], t + m.endScalars) := by
  have hle := endScalars_le m
  have c0 : ¬ (m.ownScalars == 0) = true := fun hh => hN (by
    have := beq_iff_eq.1 hh
    omega)
  have c1 : ¬ (!m.isSum) = true := by
    rw [hS]
    decide
  have c2 : ¬ (m.endScalars == 0) = true := fun hh => hN (beq_iff_eq.1 hh)
  unfold partWants
  dsimp only
  rw [if_neg c0, if_neg c1, if_neg c2, if_pos hm]

/-- Parts without a scalar of their own spend nothing. -/
theorem partsWants_idle (row idx : MsgAt) (merges : List Addr) : ∀ C : List PartAt,
    (∀ p ∈ C, p.ownScalars = 0) → ∀ j t, (partsWants row idx merges C j t).1 = []
  | [], _, _, _ => rfl
  | q :: C, h, j, t => by
    have e0 : partWants row idx (merges.contains q.addr) q j t = ([], t) := by
      unfold partWants
      dsimp only
      rw [if_pos (beq_iff_eq.2 (h q (List.Mem.head _)))]
    rw [partsWants]
    dsimp only
    rw [e0, partsWants_idle row idx merges C fun p hp => h p (List.Mem.tail _ hp)]
    rfl

/-- The stretches of a row A, m, C: no merge in A; m a merge with an end value; nothing is spent in
C. -/
theorem partsWants_merge (row idx : MsgAt) {merges : List Addr} {A C : List PartAt} {m : PartAt}
    (hA : ∀ q ∈ A, merges.contains q.addr = false) (hm : merges.contains m.addr = true)
    (hS : m.isSum = true) (hN : m.endScalars ≠ 0) (hC : ∀ p ∈ C, p.ownScalars = 0) (j t : Nat) :
    (partsWants row idx merges (A ++ m :: C) j t).1 =
      (partsWants row idx merges A j t).1 ++
        [⟨m.addr, "sum", row, j + ownScalarsOf A, m.ownScalars - m.endScalars⟩,
          ⟨m.addr, "ends", idx, t, m.endScalars⟩] := by
  rw [partsWants_append, partsWants_next, mergeEndsOf_none hA, Nat.add_zero, partsWants]
  dsimp only
  rw [partWants_merge row idx hm hS hN]
  dsimp only
  rw [partsWants_idle row idx merges C hC, List.append_nil]

/-- All of them but the last are one block of the mask row, where at least one entry of the mask row
is spent (`hpos`). -/
theorem oneStretch_merge (row idx : MsgAt) {merges : List Addr} {A : List PartAt} (m : PartAt)
    (hA : ∀ q ∈ A, merges.contains q.addr = false) (j t : Nat)
    (hpos : ownScalarsOf A + (m.ownScalars - m.endScalars) ≠ 0) :
    oneStretch (((partsWants row idx merges A j t).1 ++
        [(⟨m.addr, "sum", row, j + ownScalarsOf A, m.ownScalars - m.endScalars⟩ : Want)]).map
          (·.entry)) =
      some (row.owner, row.base.e + j, ownScalarsOf A + (m.ownScalars - m.endScalars)) := by
  have h1 := runOn_parts row idx merges A j t (row.base.e + j) 0 hA (by omega)
  have h2 : runOn row.owner (row.base.e + j) 0 (((partsWants row idx merges A j t).1 ++
      [(⟨m.addr, "sum", row, j + ownScalarsOf A, m.ownScalars - m.endScalars⟩ : Want)]).map
        (·.entry)) =
      some (0 + ownScalarsOf A + (m.ownScalars - m.endScalars)) := by
    rw [List.map_append, runOn_append _ _ _ _ _ _ h1]
    simp only [List.map_cons, List.map_nil]
    rw [runOn_one row _ _ _ _ _ _ (by omega)]
    rfl
  rw [Nat.zero_add] at h2
  exact oneStretch_of_runOn h2 hpos

end BookRow

/-! ## 4 The whole book -/

/-- **The spending entries of a link's sub-protocol are `partsWants`' own, from two numbers that are
computed from the plan.** No hypothesis on merges. -/
theorem bookWhole_row_wants {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") :
    ∃ row idx,
      ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      rowEntries B b.place (planParts b).length 0 =
        (partsWants row idx M.ends (planParts b)
          (ownScalarsOf (partsInFront F.first.blocksInOrder l b.place))
          (mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++
            partsInFront F.first.blocksInOrder l b.place))).1.map (·.entry) := by
  obtain ⟨idx, a, hidx, ha, -, hpick⟩ := pick_whole h hp hb hF
  have hord := orderOf_nodup hp
  unfold orderOf at hord
  have hn : (F.first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 hord).1).1
  obtain ⟨row, hrow, hat⟩ := linksWants_at_t _ 0 a (nodup_eraseDups _ _ (Nat.le_refl _))
    (List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨b, hb, hl⟩)) ha
  have hat' : ∀ x : Addr, x.place.link = some l →
      a.1.filter (fun w => w.spender == x) =
        (segmentWants F.first.blocksInOrder l row idx M.ends
          (0 + mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l))).1.filter
          fun w => w.spender == x := hat
  refine ⟨row, idx, hrow, hidx, ?_⟩
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
  have eT : (partsWants row idx M.ends (partsInFront F.first.blocksInOrder l b.place) 0
      (0 + mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l))).2 =
      mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place) := by
    rw [partsWants_next, mergeEndsOf_append]
    omega
  -- b's own stretches
  have hkey : ∀ j, BookRow.pick ⟨b.place, j⟩ B.ahead = BookRow.pick ⟨b.place, j⟩
      ((partsWants row idx M.ends (planParts b)
        (ownScalarsOf (partsInFront F.first.blocksInOrder l b.place))
        (mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++
          partsInFront F.first.blocksInOrder l b.place))).1.map (·.entry)) := by
    intro j
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
    have w1 : ((partsWants row idx M.ends (partsInFront F.first.blocksInOrder l b.place) 0
        (0 + mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l))).1.filter
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
    rw [hpick j, pick_entries, List.filter_append, hat' ⟨b.place, j⟩ hl, w0, List.append_nil]
    unfold segmentWants
    rw [eparts, partsWants_append, partsWants_append, List.filter_append, List.filter_append,
      w1, List.nil_append, w2, List.append_nil, eT, Nat.zero_add]
  rw [rowEntries_eq, rowPick_congr _ 0 (fun j _ => hkey j)]
  exact rowPick_parts row idx M.ends b.place
    (stretchesBy (b.rounds.map fun r => (r.entry.name, scalarsIn r)) (partsCut b)) 0
    (ownScalarsOf (partsInFront F.first.blocksInOrder l b.place))
    (mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place))

/-- **A row whose last spending part is a merge**: the row is A, m, C, with no part of A listed
among the merges, m a merge with an end value, no scalar of its own in C, and at least one entry of
the mask row spent in the row (`hpos`). All spending entries but the last are one block of the mask
row; the last is the merge's entry of the index-mask message. -/
theorem bookWhole_merge_stretch {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    (hF : ∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon")
    {A C : List PartAt} {m : PartAt} (hrow : planParts b = A ++ m :: C)
    (hA : ∀ p ∈ A, p.addr ∉ M.ends) (hm : m.addr ∈ M.ends) (hS : m.isSum = true)
    (hN : m.endScalars ≠ 0) (hC : ∀ p ∈ C, p.ownScalars = 0)
    (hpos : ownScalarsOf A + (m.ownScalars - m.endScalars) ≠ 0) :
    ∃ row idx es₁,
      ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      rowEntries B b.place (planParts b).length 0 = es₁ ++
        [(⟨m.addr, "ends", idx, mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++
          partsInFront F.first.blocksInOrder l b.place), m.endScalars⟩ : Want).entry] ∧
      oneStretch es₁ = some (row.owner,
        row.base.e + ownScalarsOf (partsInFront F.first.blocksInOrder l b.place),
        ownScalarsOf A + (m.ownScalars - m.endScalars)) := by
  obtain ⟨row, idx, hr, hi, hE⟩ := bookWhole_row_wants h hp hb hl hF
  have hAc : ∀ q ∈ A, M.ends.contains q.addr = false := fun q hq =>
    Bool.eq_false_iff.2 fun h0 => hA q hq (List.contains_iff_mem.1 h0)
  have hmc : M.ends.contains m.addr = true := List.contains_iff_mem.2 hm
  have hW := partsWants_merge row idx hAc hmc hS hN hC
    (ownScalarsOf (partsInFront F.first.blocksInOrder l b.place))
    (mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place))
  rw [← hrow] at hW
  refine ⟨row, idx, _, hr, hi, ?_, oneStretch_merge row idx m hAc
    (ownScalarsOf (partsInFront F.first.blocksInOrder l b.place))
    (mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place)) hpos⟩
  rw [hE, hW]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]

end ProofFile.Honest

#print axioms ProofFile.Honest.BookRow.partWants_next
#print axioms ProofFile.Honest.BookRow.partsWants_next
#print axioms ProofFile.Honest.linksWants_next
#print axioms ProofFile.Honest.BookRow.linksWants_at_t
#print axioms ProofFile.Honest.BookRow.partsWants_merge
#print axioms ProofFile.Honest.BookRow.oneStretch_merge
#print axioms ProofFile.Honest.bookWhole_row_wants
#print axioms ProofFile.Honest.bookWhole_merge_stretch
#print axioms ProofFile.Honest.BookRow.foldl_mergeEnds
#print axioms ProofFile.Honest.BookRow.mergeEndsOf_cons
#print axioms ProofFile.Honest.BookRow.mergeEndsOf_append
#print axioms ProofFile.Honest.BookRow.mergeEndsOf_none
#print axioms ProofFile.Honest.BookRow.segmentWants_next
#print axioms ProofFile.Honest.BookRow.partWants_merge
#print axioms ProofFile.Honest.BookRow.partsWants_idle
