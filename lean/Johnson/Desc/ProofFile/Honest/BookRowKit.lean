-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookRowKit.lean: what the parts at one place spend, maker by maker of
the book of coins (Honest/Book*.lean). Lemmas for Honest/BookRowStretch.lean. Four small
definitions.

  0  `ownScalarsOf`, `partsInFront`   the two terms of the statement: the own scalars of a list of
     parts, added up; the parts of a segment that stand in front of a place
     `pick`, `rowPick`   `spentE` (Honest/Law/Rule/Cell.lean) and `rowEntries`
     (Honest/BookStretch.lean) as functions of the list of entries alone
  1  sums of own scalars; a part's end values are among its own scalars
  2  `pick` over lists: carried entries, other spenders, the sumchecks' stretches
  3  `runOn` and `oneStretch` (Honest/BookStretch.lean) over a row of parts' stretches
  4  who spends a stretch; a row of parts' stretches, part by part, is the list itself
  5  who spends a fold's entry and the split's; a carrying entry is not spent
  6  the segments one by one; a list of sub-protocols cut at one of them

Two short names of the namespace `BookRow` are also names of `ProofFile.Honest`: `BookRow.pick` beside
`pick` (Honest/Law/Rule/RowLens.lean), `BookRow.partWants_spender` beside `partWants_spender`
(Honest/BookStart.lean). They are four different things. Write the two of this file with `BookRow.`
in front.

Limits. The lemmas are about lists, addresses, places and numbers. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookSharedLaw
import Johnson.Desc.ProofFile.Honest.BookStretch
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi S Cl : Type}

/-! ## 0 The definitions -/

/-- The own scalars of a list of parts, added up. -/
def ownScalarsOf (ps : List PartAt) : Nat := ps.foldl (fun n p => n + p.ownScalars) 0

/-- The parts of the segment number l that stand in front of a place, in the chain's order. -/
def partsInFront (bs : List (Block S Cl)) (l : Nat) (a : Place) : List PartAt :=
  ((bs.filter fun b => b.place.link == some l).takeWhile fun b => b.place != a).flatMap planParts

namespace BookRow
open ProofFile.Honest.BookShared

/-- The entries of a list by which the part at an address spends: `spentE` of the list alone. -/
abbrev pick (a : Addr) (l : List Ahead) : List Ahead :=
  (l.filter fun e => e.spender == a).filter fun e => e.once

/-- `rowEntries` of the list alone. -/
def rowPick (l : List Ahead) (p : Place) : Nat → Nat → List Ahead
  | 0, _ => []
  | n + 1, j => pick ⟨p, j⟩ l ++ rowPick l p n (j + 1)

theorem rowEntries_eq (Bk : ProverCoinCounts) (p : Place) : ∀ n j,
    rowEntries Bk p n j = rowPick Bk.ahead p n j
  | 0, _ => rfl
  | n + 1, j => by
    show spentE Bk ⟨p, j⟩ ++ rowEntries Bk p n (j + 1) =
      pick ⟨p, j⟩ Bk.ahead ++ rowPick Bk.ahead p n (j + 1)
    rw [rowEntries_eq Bk p n (j + 1)]
    rfl

/-- Two lists of which the parts from number k on spend by the same entries. -/
theorem rowPick_congr {l l' : List Ahead} {p : Place} : ∀ n k,
    (∀ j, k ≤ j → pick ⟨p, j⟩ l = pick ⟨p, j⟩ l') → rowPick l p n k = rowPick l' p n k
  | 0, _, _ => rfl
  | n + 1, k, h => by
    show pick ⟨p, k⟩ l ++ rowPick l p n (k + 1) = pick ⟨p, k⟩ l' ++ rowPick l' p n (k + 1)
    rw [h k (Nat.le_refl k), rowPick_congr n (k + 1) fun j hj => h j (Nat.le_of_succ_le hj)]

/-! ## 1 Sums -/

theorem foldl_own (ps : List PartAt) : ∀ a,
    ps.foldl (fun n p => n + p.ownScalars) a = a + ownScalarsOf ps := by
  induction ps with
  | nil => intro a; rfl
  | cons q ps ih =>
    intro a
    show List.foldl (fun n p => n + p.ownScalars) a (q :: ps) =
      a + List.foldl (fun n p => n + p.ownScalars) 0 (q :: ps)
    rw [List.foldl_cons, List.foldl_cons, ih (a + q.ownScalars), ih (0 + q.ownScalars)]
    omega

theorem ownScalarsOf_cons (q : PartAt) (ps : List PartAt) :
    ownScalarsOf (q :: ps) = q.ownScalars + ownScalarsOf ps := by
  show List.foldl (fun n p => n + p.ownScalars) 0 (q :: ps) = q.ownScalars + ownScalarsOf ps
  rw [List.foldl_cons, foldl_own]
  omega

theorem ends_le : ∀ (rs : List (String × Nat)) (a b : Nat), a ≤ b →
    rs.foldl (fun n r => if r.1 == "PSC values" then n + r.2 else n) a ≤
      rs.foldl (fun n r => if frameNames.contains r.1 then n else n + r.2) b
  | [], _, _, h => h
  | r :: rs, a, b, h => by
    rw [List.foldl_cons, List.foldl_cons]
    apply ends_le rs
    by_cases h1 : (r.1 == "PSC values") = true
    · have e : r.1 = "PSC values" := beq_iff_eq.1 h1
      have h2 : frameNames.contains r.1 = false := by
        rw [e]
        decide
      rw [if_pos h1, h2]
      show a + r.2 ≤ b + r.2
      omega
    · rw [if_neg h1]
      split <;> omega

theorem endScalars_le (q : PartAt) : q.endScalars ≤ q.ownScalars :=
  ends_le q.rounds 0 0 (Nat.le_refl 0)

/-! ## 2 `pick` -/

theorem pick_append (a : Addr) (l l' : List Ahead) : pick a (l ++ l') = pick a l ++ pick a l' := by
  simp only [pick, List.filter_append]

theorem pick_carried {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.once = false) : pick a l = [] :=
  List.filter_eq_nil_iff.2 fun e he => by
    have h1 := h e (List.mem_filter.1 he).1
    simp [h1]

theorem pick_other {a : Addr} {l : List Ahead} (h : ∀ e ∈ l, e.spender ≠ a) : pick a l = [] := by
  have h0 : l.filter (fun e => e.spender == a) = [] :=
    List.filter_eq_nil_iff.2 fun e he => by
      have hne := h e he
      simp [hne]
  show (l.filter fun e => e.spender == a).filter (fun e => e.once) = []
  rw [h0]
  rfl

theorem pick_entries (a : Addr) (ws : List Want) :
    pick a (ws.map (·.entry)) = (ws.filter fun w => w.spender == a).map (·.entry) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    have e1 : w.entry.spender = w.spender := rfl
    have e2 : w.entry.once = true := rfl
    by_cases h : w.spender = a
    · simpa [pick, List.filter_cons, e1, e2, h] using ih
    · simpa [pick, List.filter_cons, e1, e2, h] using ih

theorem wants_other {a : Addr} {ws : List Want} (h : ∀ w ∈ ws, w.spender ≠ a) :
    ws.filter (fun w => w.spender == a) = [] :=
  List.filter_eq_nil_iff.2 fun w hw => by
    have hne := h w hw
    simp [hne]

theorem wants_all {a : Addr} {ws : List Want} (h : ∀ w ∈ ws, w.spender = a) :
    ws.filter (fun w => w.spender == a) = ws :=
  List.filter_eq_self.2 fun w hw => by
    have he := h w hw
    simp [he]

/-! ## 3 One stretch -/

theorem runOn_one (row : MsgAt) (sp : Addr) (use : String) (s c j n : Nat)
    (h : s + c = row.base.e + j) (rest : List Ahead) :
    runOn row.owner s c ((⟨sp, use, row, j, n⟩ : Want).entry :: rest) =
      runOn row.owner s (c + n) rest := by
  have hstart : (row.base.plus ⟨0, j⟩).e = s + c := by
    rw [h]
  rw [runOn]
  split
  · rfl
  · rename_i hn
    exact absurd ⟨rfl, hstart⟩ hn

theorem runOn_append (o : Addr) (s : Nat) : ∀ (A B : List Ahead) (c c' : Nat),
    runOn o s c A = some c' → runOn o s c (A ++ B) = runOn o s c' B
  | [], B, c, c', h => by
    have e : c = c' := Option.some.inj h
    rw [e]
    rfl
  | f :: A, B, c, c', h => by
    rw [List.cons_append, runOn]
    rw [runOn] at h
    split at h
    · rename_i hc
      rw [if_pos hc]
      exact runOn_append o s A B _ _ h
    · cases h

/-- A part that lays its end values under its segment's row: its stretches stand in a row. -/
theorem runOn_part (row idx : MsgAt) (q : PartAt) (j t s c : Nat) (merge : Bool)
    (hm : merge = false) (h : s + c = row.base.e + j) :
    runOn row.owner s c ((partWants row idx merge q j t).1.map (·.entry)) =
      some (c + q.ownScalars) := by
  have hle := endScalars_le q
  unfold partWants
  dsimp only
  split
  · rename_i h0
    have e0 : q.ownScalars = 0 := beq_iff_eq.1 h0
    rw [e0]
    rfl
  · split
    · simp only [List.map_cons, List.map_nil]
      rw [runOn_one row _ _ s c j _ h]
      rfl
    · split
      · simp only [List.map_cons, List.map_nil]
        rw [runOn_one row _ _ s c j _ h]
        rfl
      · split
        · rename_i hf
          rw [hm] at hf
          cases hf
        · simp only [List.map_cons, List.map_nil]
          rw [runOn_one row _ _ s c j _ h, runOn_one row _ _ s _ _ _ (by omega)]
          show some (c + (q.ownScalars - q.endScalars) + q.endScalars) = some (c + q.ownScalars)
          congr 1
          omega

theorem runOn_parts (row idx : MsgAt) (merges : List Addr) :
    ∀ (ps : List PartAt) (j t s c : Nat), (∀ q ∈ ps, merges.contains q.addr = false) →
      s + c = row.base.e + j →
      runOn row.owner s c ((partsWants row idx merges ps j t).1.map (·.entry)) =
        some (c + ownScalarsOf ps)
  | [], _, _, _, _, _, _ => rfl
  | q :: ps, j, t, s, c, hno, h => by
    rw [partsWants]
    dsimp only
    rw [List.map_append,
      runOn_append _ _ _ _ _ _ (runOn_part row idx q j t s c _ (hno q (List.Mem.head _)) h),
      runOn_parts row idx merges ps _ _ s _ (fun q' hq' => hno q' (List.Mem.tail _ hq'))
        (by omega),
      ownScalarsOf_cons]
    congr 1
    omega

theorem oneStretch_of_runOn {o : Addr} {s c : Nat} : ∀ {L : List Ahead},
    runOn o s 0 L = some c → c ≠ 0 → oneStretch L = some (o, s, c)
  | [], h, hc => absurd (Option.some.inj h).symm hc
  | e :: es, h, _ => by
    rw [runOn] at h
    split at h
    · rename_i hc
      obtain ⟨ho, hs⟩ := hc
      show (runOn e.owner e.start.e e.count.e es).map (fun c => (e.owner, e.start.e, c)) =
        some (o, s, c)
      rw [ho, hs]
      simp only [Nat.add_zero, Nat.zero_add] at h ⊢
      rw [h]
      rfl
    · cases h

/-! ## 4 Who spends a stretch -/

theorem partWants_spender (row idx : MsgAt) (merge : Bool) (p : PartAt) (j t : Nat) :
    ∀ w ∈ (partWants row idx merge p j t).1, w.spender = p.addr := by
  intro w hw
  unfold partWants at hw
  dsimp only at hw
  split at hw
  · cases hw
  · split at hw
    · rw [mem_one hw]
    · split at hw
      · rw [mem_one hw]
      · split at hw
        · rcases mem_two hw with e | e
          · rw [e]
          · rw [e]
        · rcases mem_two hw with e | e
          · rw [e]
          · rw [e]

theorem partsWants_spender (row idx : MsgAt) (merges : List Addr) :
    ∀ (ps : List PartAt) (j t : Nat), ∀ w ∈ (partsWants row idx merges ps j t).1,
      ∃ q ∈ ps, w.spender = q.addr
  | [], _, _, w, hw => by
    unfold partsWants at hw
    try dsimp only at hw
    cases hw
  | p :: ps, j, t, w, hw => by
    unfold partsWants at hw
    try dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · exact ⟨p, List.Mem.head _, partWants_spender _ _ _ _ _ _ w h⟩
    · obtain ⟨q, hq, e⟩ := partsWants_spender row idx merges ps _ _ w h
      exact ⟨q, List.Mem.tail _ hq, e⟩

theorem loneWants_spender (idx : MsgAt) (lone : List Addr) :
    ∀ (ps : List PartAt) (t : Nat), ∀ w ∈ (loneWants idx lone ps t).1,
      ∃ q ∈ ps, w.spender = q.addr
  | [], _, w, hw => by
    unfold loneWants at hw
    try dsimp only at hw
    cases hw
  | p :: ps, t, w, hw => by
    unfold loneWants at hw
    try dsimp only at hw
    rcases List.mem_append.1 hw with h | h
    · refine ⟨p, List.Mem.head _, ?_⟩
      split at h
      · unfold loneSumWants at h
        split at h
        · rw [mem_one h]
        · try dsimp only at h
          cases h
      · try dsimp only at h
        cases h
    · obtain ⟨q, hq, e⟩ := loneWants_spender idx lone ps _ w h
      exact ⟨q, List.Mem.tail _ hq, e⟩

theorem partsWants_append (row idx : MsgAt) (merges : List Addr) (C : List PartAt) :
    ∀ (A : List PartAt) (j t : Nat),
      (partsWants row idx merges (A ++ C) j t).1 =
        (partsWants row idx merges A j t).1 ++
          (partsWants row idx merges C (j + ownScalarsOf A)
            (partsWants row idx merges A j t).2).1
  | [], _, _ => rfl
  | q :: A, j, t => by
    have e : j + ownScalarsOf (q :: A) = j + q.ownScalars + ownScalarsOf A := by
      rw [ownScalarsOf_cons]
      omega
    rw [List.cons_append, partsWants, partsWants]
    dsimp only
    rw [partsWants_append row idx merges C A, e, List.append_assoc]

theorem planParts_place {b : Block S Cl} {q : PartAt} (h : q ∈ planParts b) :
    q.addr.place = b.place := by
  unfold planParts at h
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 h
  rfl

/-- The parts that are numbered from k on stand at numbers from k on. -/
theorem numbered_from (p : Place) : ∀ (L : List (List (String × Nat))) (k : Nat),
    ∀ q ∈ (L.zipIdx k).map (fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)), ∃ i, k ≤ i ∧ q.addr = ⟨p, i⟩
  | [], _, q, hq => by cases hq
  | r :: L, k, q, hq => by
    rw [List.zipIdx_cons, List.map_cons] at hq
    cases hq with
    | head => exact ⟨k, Nat.le_refl k, rfl⟩
    | tail _ h2 =>
      obtain ⟨i, hi, e⟩ := numbered_from p L (k + 1) q h2
      exact ⟨i, Nat.le_of_succ_le hi, e⟩

/-- **The stretches of a row of parts, taken part by part, are the list itself.** -/
theorem rowPick_parts (row idx : MsgAt) (merges : List Addr) (p : Place) :
    ∀ (L : List (List (String × Nat))) (k j t : Nat),
      rowPick ((partsWants row idx merges
          ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)) j t).1.map (·.entry)) p
        ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)).length k =
      (partsWants row idx merges
          ((L.zipIdx k).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt)) j t).1.map (·.entry)
  | [], _, _, _ => rfl
  | r :: L, k, j, t => by
    rw [List.zipIdx_cons, List.map_cons, List.length_cons, partsWants]
    dsimp only
    have hx : ∀ w ∈ (partWants row idx (merges.contains ⟨p, k⟩) ⟨⟨p, k⟩, r⟩ j t).1,
        w.spender = ⟨p, k⟩ := partWants_spender _ _ _ _ _ _
    have hy : ∀ w ∈ (partsWants row idx merges
        ((L.zipIdx (k + 1)).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt))
        (j + (⟨⟨p, k⟩, r⟩ : PartAt).ownScalars)
        (partWants row idx (merges.contains ⟨p, k⟩) ⟨⟨p, k⟩, r⟩ j t).2).1,
        ∃ i, k + 1 ≤ i ∧ w.spender = ⟨p, i⟩ := by
      intro w hw
      obtain ⟨q, hq, e⟩ := partsWants_spender _ _ _ _ _ _ w hw
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
      rowPick_congr _ (k + 1) (l' := (partsWants row idx merges
        ((L.zipIdx (k + 1)).map fun x => (⟨⟨p, x.2⟩, x.1⟩ : PartAt))
        (j + (⟨⟨p, k⟩, r⟩ : PartAt).ownScalars)
        (partWants row idx (merges.contains ⟨p, k⟩) ⟨⟨p, k⟩, r⟩ j t).2).1.map (·.entry))
        (by
          intro i hi
          rw [pick_append, pick_entries, wants_other (by
            intro w hw
            rw [hx w hw]
            intro h0
            have h1 : k = i := congrArg Addr.part h0
            omega)]
          rfl),
      rowPick_parts row idx merges p L (k + 1)]

/-! ## 5 The folds, the split, the carrying entries -/

theorem dropWhile_head {α : Type} (p : α → Bool) : ∀ (l : List α) (a : α) (t : List α),
    l.dropWhile p = a :: t → a ∈ l ∧ p a = false
  | [], _, _, h => by cases h
  | x :: l, a, t, h => by
    by_cases hx : p x = true
    · rw [List.dropWhile_cons_of_pos hx] at h
      obtain ⟨h1, h2⟩ := dropWhile_head p l a t h
      exact ⟨List.Mem.tail _ h1, h2⟩
    · rw [List.dropWhile_cons_of_neg hx] at h
      cases h
      exact ⟨List.Mem.head _, by simpa using hx⟩

theorem foldBehind_name {l : List PlanB} {i e : Nat} {r : Bool} {k : Nat}
    (h : foldBehind l i = some (e, r, k)) :
    ∃ d, (l.flatMap (·.rounds))[e]? = some d ∧ d.entry.name = "FOLD epsilon" := by
  unfold foldBehind at h
  dsimp only at h
  split at h
  · cases h
  · rename_i x u hx
    have e1 := Option.some.inj h
    have e2 : x.2 = e := congrArg Prod.fst e1
    obtain ⟨hm, hp⟩ := dropWhile_head _ _ _ _ hx
    have hg := List.mem_zipIdx_iff_getElem?.1 (List.mem_of_mem_drop hm)
    refine ⟨x.1, e2 ▸ hg, ?_⟩
    simpa using hp

theorem addrIn_holds : ∀ (l : List PlanB) (i : Nat) (a : Addr) (d : Fmt.DeclaredRound),
    addrIn l i = some a → (l.flatMap (·.rounds))[i]? = some d →
      ∃ x ∈ l, x.place = a.place ∧ d ∈ x.rounds
  | [], _, _, _, h, _ => by
    unfold addrIn at h
    cases h
  | b :: l, i, a, d, h, hd => by
    unfold addrIn at h
    rw [List.flatMap_cons] at hd
    split at h
    · rename_i hi
      have e := Option.some.inj h
      rw [List.getElem?_append_left hi] at hd
      exact ⟨b, List.Mem.head _, by rw [← e], List.mem_of_getElem? hd⟩
    · rename_i hi
      rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hd
      obtain ⟨x, hx, h1, h2⟩ := addrIn_holds l _ a d h hd
      exact ⟨x, List.Mem.tail _ hx, h1, h2⟩

/-- A fold's spending entry is spent at a sub-protocol that holds a round "FOLD epsilon". -/
theorem foldEntries_spender {here later : List PlanB} {c : Johnson.G.ChainSends} {l : List Ahead}
    (h : foldEntries here later c = .ok l) :
    ∀ e ∈ l, ∃ x ∈ here ++ later, x.place = e.spender.place ∧
      ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon" := by
  unfold foldEntries at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨ll, hll, e⟩ := ex_map h
    intro a ha
    rw [← e] at ha
    obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
    refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, ∃ x ∈ here ++ later,
      x.place = a.spender.place ∧ ∃ d ∈ x.rounds, d.entry.name = "FOLD epsilon") ?_ hll
      inner hin a ha
    intro x _ r hr
    refine mapM_all _ r ?_ hr
    intro j _ b hb
    try dsimp only at hb
    split at hb
    · cases hb
    · cases hb
    · rename_i e' k hfb
      split at hb
      · rename_i o p st ho hp hst
        have e2 := Except.ok.inj hb
        obtain ⟨d, hd, hn⟩ := foldBehind_name hfb
        obtain ⟨y, hy, hy1, hy2⟩ := addrIn_holds _ _ _ _ hp hd
        rw [← e2]
        exact ⟨y, hy, hy1, d, hy2, hn⟩
      · cases hb

theorem splitEntry_spender {bs : List (Block S Cl)} {c : Johnson.G.ChainSends} {e : Ahead}
    (h : splitEntry bs c = some e) : e.spender.place ∈ bs.map (·.place) := by
  unfold splitEntry at h
  dsimp only at h
  obtain ⟨p, hp, h⟩ := opt_bind h
  obtain ⟨m, -, h⟩ := opt_map h
  rw [← h]
  exact addrOfRound_place _ _ _ hp

theorem carryPair_once {p q : Addr} {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, e.once = false := by
  intro e he
  unfold carryPair at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    rfl
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    rfl

theorem groupCarries_once {l : List PlanB} {i : Nat} {g : List SentMsg} {own : Option SentMsg}
    {r : List Ahead} (h : groupCarries l i g own = .ok r) : ∀ e ∈ r, e.once = false := by
  unfold groupCarries at h
  split at h
  · have e := Except.ok.inj h
    rw [← e]
    exact carryPair_once
  · cases h

theorem segmentCarries_once {here : List PlanB} {ms : List SentMsg} {l : List Ahead}
    (h : segmentCarries here ms = .ok l) : ∀ e ∈ l, e.once = false := by
  unfold segmentCarries at h
  obtain ⟨ll, hll, e⟩ := ex_map h
  intro a ha
  rw [← e] at ha
  obtain ⟨inner, hin, ha⟩ := List.mem_flatten.1 ha
  refine mapM_all _ ll (P := fun inner => ∀ a ∈ inner, a.once = false) ?_ hll inner hin a ha
  intro f _ r hr
  try dsimp only at hr
  split at hr
  · have e2 := Except.ok.inj hr
    rw [← e2]
    intro a ha
    rcases List.mem_append.1 ha with h1 | h1
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      rfl
    · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h1
      rfl
  · cases hr

/-! ## 6 The segments; a list cut at one of its members -/

theorem segmentWants_link (bs : List (Block S Cl)) (l : Nat) (row idx : MsgAt)
    (merges : List Addr) (t : Nat) :
    ∀ w ∈ (segmentWants bs l row idx merges t).1, w.spender.place.link = some l := by
  intro w hw
  obtain ⟨q, hq, e⟩ := partsWants_spender row idx merges _ 0 t w hw
  obtain ⟨x, hx, hq2⟩ := List.mem_flatMap.1 hq
  rw [e, planParts_place hq2]
  exact beq_iff_eq.1 (List.mem_filter.1 hx).2

/-- Where the segment number l is not among the segments listed, no stretch is spent in it. -/
theorem linksWants_none {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} {l : Nat} :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat), l ∉ ls →
      linksWants bs c later idx merges ls t = .ok r →
      ∀ w ∈ r.1, w.spender.place.link ≠ some l
  | [], t, r, _, h, w, hw => by
    unfold linksWants at h
    have e := Except.ok.inj h
    rw [← e] at hw
    cases hw
  | l' :: ls, t, r, hl, h, w, hw => by
    unfold linksWants at h
    split at h
    · cases h
    · rename_i row hrow
      try dsimp only at h
      obtain ⟨y, hy, e⟩ := ex_mapE h
      rw [← e] at hw
      rcases List.mem_append.1 hw with h1 | h1
      · rw [segmentWants_link bs l' row idx merges t w h1]
        intro h0
        exact hl (Option.some.inj h0 ▸ List.Mem.head _)
      · exact linksWants_none ls _ y (fun h0 => hl (List.Mem.tail _ h0)) hy w h1

/-- **Of all segments' stretches those that are spent in the segment number l are that segment's.**
-/
theorem linksWants_at {bs : List (Block S Cl)} {c : Johnson.G.ChainSends}
    {later : List Fmt.DeclaredRound} {idx : MsgAt} {merges : List Addr} {l : Nat} :
    ∀ (ls : List Nat) (t : Nat) (r : List Want × Nat), ls.Nodup → l ∈ ls →
      linksWants bs c later idx merges ls t = .ok r →
      ∃ row t', ownerOf maskRowRun bs c later s!"link {l}, moment 0" isMaskRowMsg = some row ∧
        ∀ a : Addr, a.place.link = some l →
          r.1.filter (fun w => w.spender == a) =
            (segmentWants bs l row idx merges t').1.filter fun w => w.spender == a
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
        refine ⟨row, t, hrow, fun a ha => ?_⟩
        rw [← e]
        show (_ ++ y.1).filter _ = _
        rw [List.filter_append, wants_other (ws := y.1) (by
          intro w hw h0
          exact linksWants_none ls _ y hn1 hy w hw (h0 ▸ ha)), List.append_nil]
      · have hl2 : l ∈ ls := by
          cases hl with
          | head => exact absurd rfl hll
          | tail _ h2 => exact h2
        obtain ⟨row2, t2, hr2, hf2⟩ := linksWants_at ls _ y hn2 hl2 hy
        refine ⟨row2, t2, hr2, fun a ha => ?_⟩
        rw [← e]
        show (_ ++ y.1).filter _ = _
        rw [List.filter_append, wants_other (by
          intro w hw h0
          have h3 := segmentWants_link bs l' row idx merges t w hw
          rw [h0, ha] at h3
          exact hll (Option.some.inj h3).symm), List.nil_append]
        exact hf2 a ha

theorem nodup_eraseDups : ∀ (n : Nat) (l : List Nat), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => absurd h (Nat.not_succ_le_zero _)
  | n + 1, a :: l, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨?_, nodup_eraseDups n _
      (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ h))⟩
    intro hm
    have h2 := (List.mem_filter.1 (List.mem_eraseDups.1 hm)).2
    simp at h2

theorem nodup_filter_map {α β : Type} (f : α → β) (p : α → Bool) : ∀ l : List α,
    (l.map f).Nodup → ((l.filter p).map f).Nodup
  | [], h => h
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    by_cases hp : p a = true
    · rw [List.filter_cons_of_pos hp, List.map_cons, List.nodup_cons]
      refine ⟨fun hm => h.1 ?_, nodup_filter_map f p l h.2⟩
      obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
      exact List.mem_map.2 ⟨y, (List.mem_filter.1 hy).1, e⟩
    · rw [List.filter_cons_of_neg hp]
      exact nodup_filter_map f p l h.2

/-- A list of sub-protocols at places without a twin, cut at one of them. -/
theorem cut_at {b : Block S Cl} : ∀ (bs : List (Block S Cl)), (bs.map (·.place)).Nodup → b ∈ bs →
    ∃ t, bs = bs.takeWhile (fun x => x.place != b.place) ++ b :: t ∧
      (∀ x ∈ bs.takeWhile (fun x => x.place != b.place), x.place ≠ b.place) ∧
      ∀ x ∈ t, x.place ≠ b.place
  | [], _, hb => by cases hb
  | x :: bs, hn, hb => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hx : x.place = b.place
    · have hxb : b = x := by
        cases hb with
        | head => rfl
        | tail _ h2 => exact absurd (List.mem_map.2 ⟨b, h2, hx.symm⟩) hn.1
      subst hxb
      have h0 : ¬ ((fun y : Block S Cl => y.place != b.place) b = true) := by simp
      rw [List.takeWhile_cons_of_neg (p := fun y : Block S Cl => y.place != b.place) (a := b) h0]
      refine ⟨bs, rfl, (fun y hy => by cases hy), fun y hy e =>
        hn.1 (List.mem_map.2 ⟨y, hy, e⟩)⟩
    · have hb2 : b ∈ bs := by
        cases hb with
        | head => exact absurd rfl hx
        | tail _ h2 => exact h2
      obtain ⟨t, e, h1, h2⟩ := cut_at bs hn.2 hb2
      have h0 : (fun y : Block S Cl => y.place != b.place) x = true := by simp [hx]
      rw [List.takeWhile_cons_of_pos (p := fun y : Block S Cl => y.place != b.place) (a := x) h0]
      refine ⟨t, by rw [List.cons_append, ← e], ?_, h2⟩
      intro y hy
      cases hy with
      | head => exact hx
      | tail _ h3 => exact h1 y h3

end BookRow

end ProofFile.Honest

#print axioms ProofFile.Honest.BookRow.rowEntries_eq
#print axioms ProofFile.Honest.BookRow.rowPick_congr
#print axioms ProofFile.Honest.BookRow.foldl_own
#print axioms ProofFile.Honest.BookRow.ownScalarsOf_cons
#print axioms ProofFile.Honest.BookRow.ends_le
#print axioms ProofFile.Honest.BookRow.endScalars_le
#print axioms ProofFile.Honest.BookRow.pick_append
#print axioms ProofFile.Honest.BookRow.pick_carried
#print axioms ProofFile.Honest.BookRow.pick_other
#print axioms ProofFile.Honest.BookRow.pick_entries
#print axioms ProofFile.Honest.BookRow.wants_other
#print axioms ProofFile.Honest.BookRow.wants_all
#print axioms ProofFile.Honest.BookRow.runOn_one
#print axioms ProofFile.Honest.BookRow.runOn_append
#print axioms ProofFile.Honest.BookRow.runOn_part
#print axioms ProofFile.Honest.BookRow.runOn_parts
#print axioms ProofFile.Honest.BookRow.oneStretch_of_runOn
#print axioms ProofFile.Honest.BookRow.partWants_spender
#print axioms ProofFile.Honest.BookRow.partsWants_spender
#print axioms ProofFile.Honest.BookRow.loneWants_spender
#print axioms ProofFile.Honest.BookRow.partsWants_append
#print axioms ProofFile.Honest.BookRow.planParts_place
#print axioms ProofFile.Honest.BookRow.numbered_from
#print axioms ProofFile.Honest.BookRow.rowPick_parts
#print axioms ProofFile.Honest.BookRow.dropWhile_head
#print axioms ProofFile.Honest.BookRow.foldBehind_name
#print axioms ProofFile.Honest.BookRow.addrIn_holds
#print axioms ProofFile.Honest.BookRow.foldEntries_spender
#print axioms ProofFile.Honest.BookRow.splitEntry_spender
#print axioms ProofFile.Honest.BookRow.carryPair_once
#print axioms ProofFile.Honest.BookRow.groupCarries_once
#print axioms ProofFile.Honest.BookRow.segmentCarries_once
#print axioms ProofFile.Honest.BookRow.segmentWants_link
#print axioms ProofFile.Honest.BookRow.linksWants_none
#print axioms ProofFile.Honest.BookRow.linksWants_at
#print axioms ProofFile.Honest.BookRow.nodup_eraseDups
#print axioms ProofFile.Honest.BookRow.nodup_filter_map
#print axioms ProofFile.Honest.BookRow.cut_at
