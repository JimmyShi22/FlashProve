-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/KeepsMsgs.lean: AT A YES OF EACH OF THE SIX BLOCKS OF THE SHARED CHAIN's PLACE
THAT SEND NOTHING, EVERY MESSAGE OF THE STATEMENT KEEPS ITS SHAPE, ITS MARK "SAMPLED" AND ITS SAMPLE
ROWS, AND NO MESSAGE COMES: the sending kind's SameMsgs (Johnson/Desc/K1/Law/SeedIs.lean).

Why. A pin reads, of a message, the columns of its tree and its sample in the record. That the word
stays past a block is a fact on the strings. THAT THE RECORD BEHIND THE BLOCK STILL HOLDS THE SAMPLE
IS THE BLOCK's DUTY: here it is paid for "LIN point", "(rec_gamma)", "LOC", the joinings, "LIN zeta"
and "SPLIT". At the two sendings it is the sending kind's own law.
  same_newGroupP, same_joinP, same_addRowP, same_addRowsP, same_takeMaskP   the ground's five steps
                  that these six blocks take.
  msgs_point, msgs_rec, msgs_loc, msgs_joins, msgs_split   the places.
  msgs_of_blocks  **the six blocks.**
  SameBook, book_of_blocks   and the book of trees and the count of roots are as they were: so what
                  a clause on the record's book says in front of such a block it says behind it.

What is not claimed. Nothing on the groups, the ledgers or the open rows, which these blocks do
turn. same_trans and same_joinP are TWINS BY NEED of the sending kind's SameMsgs.trans and
joinP_msgs, which stand in a file whose imports reach the first chain's whole state: they fall when
these two are cut free. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.PointGood
import Johnson.Desc.Means.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (SameMsgs)

/-- Nothing turned. -/
theorem same_refl (T : Statement) : SameMsgs T T := ⟨rfl, fun _ => rfl⟩

/-- One step behind another. -/
theorem same_trans {A B C : Statement} (h1 : SameMsgs A B) (h2 : SameMsgs B C) : SameMsgs A C :=
  ⟨h2.1.trans h1.1, fun j => (h2.2 j).trans (h1.2 j)⟩

/-- One more group. -/
theorem same_newGroupP (d d' : St) (c mc n : Nat) (h : newGroupP d c mc = some (n, d')) :
    SameMsgs d.st d'.st := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, fun _ => rfl⟩
  · cases h

/-- A message joins a group. -/
theorem same_joinP (d d' : St) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    SameMsgs d.st d'.st := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, fun j => Means.map_modify _ _ _ _ _ fun _ => rfl⟩
  · cases h

/-- One more open row. -/
theorem same_addRowP (d d' : St) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    SameMsgs d.st d'.st := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ => rfl⟩
  · cases h

/-- Open rows, one by one. -/
theorem same_addRowsFrom (g : Nat) (rows : List Row) : ∀ d d' : St,
    addRowsFrom g rows d = some d' → SameMsgs d.st d'.st := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact same_refl _
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    exact same_trans (same_addRowP d d1 g row h1) (ih d1 d' h2)

/-- Open rows. -/
theorem same_addRowsP (d d' : St) (g : Nat) (rows : List Row) (h : addRowsP d g rows = some d') :
    SameMsgs d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact same_addRowsFrom g rows d d' h
  · cases h

/-- The next free mask entry. -/
theorem same_takeMaskP (d d' : St) (o n : Nat) (h : takeMaskP d o = some (n, d')) :
    SameMsgs d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, fun j => Means.map_modify _ _ _ _ _ fun _ => rfl⟩
  · cases h

/-- "LIN point". -/
theorem msgs_point (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') :
    SameMsgs d.st d'.st := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    have s1 := same_newGroupP d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      exact same_trans s1 (same_newGroupP d1 d2 _ _ gO h3)
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨_, rfl⟩ := h3
      exact s1
  · cases h

/-- "(rec_gamma)". -/
theorem msgs_rec (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d') :
    SameMsgs d.st d'.st := by
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := h
  exact same_trans (same_joinP d d1 _ _ _ hj) (same_addRowsP d1 d' _ rows ha)

/-- "LOC". -/
theorem msgs_loc (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (h : loc p d [r] [cols] = some d') : SameMsgs d.st d'.st := by
  unfold loc at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rows, _, ha⟩ := h
  exact same_addRowsP d d' _ rows ha

/-- The joinings. -/
theorem msgs_joins (p : Par) (d d' : St) (rs : List Fmt.RoundView) (h : joins p d rs = some d') :
    SameMsgs d.st d'.st := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, h1, h2⟩ := h
  have s1 := same_joinP d d1 _ _ _ h1
  split at h2
  · simp only [Option.bind_eq_some_iff] at h2
    obtain ⟨d2, h3, h4⟩ := h2
    exact same_trans (same_trans s1 (same_joinP d1 d2 _ _ _ h3)) (same_joinP d2 d' _ _ _ h4)
  · simp only [Option.some.injEq] at h2
    subst h2
    exact s1

/-- "SPLIT", two codes. -/
theorem msgs_split (p : Par) (d d' : St) (r : Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : split p d [r] = some d') : SameMsgs d.st d'.st := by
  obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv p d d' r hS h
  exact same_trans (same_trans (same_takeMaskP d d₁ _ _ hk) (same_addRowP d₁ d₂ _ _ h2))
    (same_addRowP d₂ d' _ _ h3)

/-! ## The book of trees and the count of roots -/

/-- The book of trees and the count of roots are as they were. -/
def SameBook (d d' : St) : Prop := d'.book = d.book ∧ d'.roots = d.roots

/-- One step behind another. -/
theorem SameBook.trans {a b c : St} (h1 : SameBook a b) (h2 : SameBook b c) : SameBook a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- One more group. -/
theorem book_newGroupP (d d' : St) (c mc n : Nat) (h : newGroupP d c mc = some (n, d')) :
    SameBook d d' := by
  unfold newGroupP at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · cases h

/-- A message joins a group. -/
theorem book_joinP (d d' : St) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d') :
    SameBook d d' := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · cases h

/-- One more open row. -/
theorem book_addRowP (d d' : St) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    SameBook d d' := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  · cases h

/-- Open rows, one by one. -/
theorem book_addRowsFrom (g : Nat) (rows : List Row) : ∀ d d' : St,
    addRowsFrom g rows d = some d' → SameBook d d' := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl⟩
  | cons row l ih =>
    intro d d' h
    simp only [addRowsFrom, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    exact (book_addRowP d d1 g row h1).trans (ih d1 d' h2)

/-- Open rows. -/
theorem book_addRowsP (d d' : St) (g : Nat) (rows : List Row) (h : addRowsP d g rows = some d') :
    SameBook d d' := by
  unfold addRowsP at h
  split at h
  · exact book_addRowsFrom g rows d d' h
  · cases h

/-- The next free mask entry. -/
theorem book_takeMaskP (d d' : St) (o n : Nat) (h : takeMaskP d o = some (n, d')) :
    SameBook d d' := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => simp [hl] at h
    | some l =>
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  · cases h

/-- **At a yes of each of the six blocks that send nothing the book of trees and the count of roots
are as they were**; two codes. -/
theorem book_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) :
    ∀ b ∈ [b1, b3, b4, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' → SameBook d d' := by
  have hq := quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  intro b hb d rs gs d' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · have k := point_of_blocks P _ b2 b3 b4 b5 b6 b7 b8 hbl d rs gs d' h
    unfold linPoint at k
    split at k
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at k
      obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := k
      have s1 := book_newGroupP d d1 _ _ gU h1
      split at h2
      · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
        obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
        exact s1.trans (book_newGroupP d1 d2 _ _ gO h3)
      · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
        obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
        simp only [Prod.mk.injEq] at h3
        obtain ⟨_, rfl⟩ := h3
        exact s1
    · cases k
  · have k := hq.1 d rs gs d' h
    unfold laysRec at k
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at k
    obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := k
    exact (book_joinP d d1 _ _ _ hj).trans (book_addRowsP d1 d' _ rows ha)
  · have k := loc_of_blocks P b1 b2 b3 _ b5 b6 b7 b8 hbl d rs gs d' h
    obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k
    rw [hr, hg] at k
    unfold loc at k
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at k
    obtain ⟨rows, _, ha⟩ := k
    exact book_addRowsP d d' _ rows ha
  · have k := hq.2 d rs gs d' h
    unfold joins at k
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at k
    obtain ⟨u0, _, d1, h1, h2⟩ := k
    have s1 := book_joinP d d1 _ _ _ h1
    split at h2
    · simp only [Option.bind_eq_some_iff] at h2
      obtain ⟨d2, h3, h4⟩ := h2
      exact (s1.trans (book_joinP d1 d2 _ _ _ h3)).trans (book_joinP d2 d' _ _ _ h4)
    · simp only [Option.some.injEq] at h2
      subst h2
      exact s1
  · have k := zeta_of_blocks P b1 b2 b3 b4 b5 b6 _ b8 hbl d rs gs d' h
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k
    rw [hr] at k
    rw [linZeta_inv d d' r7 k]
    exact ⟨rfl, rfl⟩
  · have k := decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 _ hbl d rs gs d' h
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k
    rw [hr] at k
    obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv P.par d d' r8 hS k
    exact ((book_takeMaskP d d₁ _ _ hk).trans (book_addRowP d₁ d₂ _ _ h2)).trans
      (book_addRowP d₂ d' _ _ h3)

/-- **At a yes of each of the six blocks that send nothing every message keeps its shape, its mark
and its sample rows, and no message comes**; two codes. -/
theorem msgs_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) :
    ∀ b ∈ [b1, b3, b4, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      SameMsgs d.st d'.st := by
  have hq := quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  intro b hb d rs gs d' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact msgs_point P.par d d' rs (point_of_blocks P _ b2 b3 b4 b5 b6 b7 b8 hbl d rs gs d' h)
  · exact msgs_rec P.par d d' rs (hq.1 d rs gs d' h)
  · have k := loc_of_blocks P b1 b2 b3 _ b5 b6 b7 b8 hbl d rs gs d' h
    obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k
    rw [hr, hg] at k
    exact msgs_loc P.par d d' r4 cols k
  · exact msgs_joins P.par d d' rs (hq.2 d rs gs d' h)
  · have k := zeta_of_blocks P b1 b2 b3 b4 b5 b6 _ b8 hbl d rs gs d' h
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k
    rw [hr] at k
    rw [linZeta_inv d d' r7 k]
    exact same_refl _
  · have k := decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 _ hbl d rs gs d' h
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k
    rw [hr] at k
    exact msgs_split P.par d d' r8 hS k

end Desc.K14.Law
