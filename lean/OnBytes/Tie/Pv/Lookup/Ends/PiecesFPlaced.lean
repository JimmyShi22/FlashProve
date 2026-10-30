-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Ends/PiecesFPlaced.lean: wherever piecesF (OnBytes/Model/Tail.lean) returns a
record, the pieces of its two lookup calls pass the two tests of
OnBytes/Tie/Pv/Lookup/Ends/FoTailNums.lean.

Statements and proofs, on the bodies of piecesF, t2BL (OnBytes/Model/Tail.lean) and placeZ
(OnBytes/Model/Forest.lean), routines of the Lean verifier under OnBytes/.
Main names, each with the one premise tl0.piecesF = .ok tl, for either call q:
  `piecesF_pieceOK`: each piece of call q meets PieceOK at the call's own number of bits.
  `piecesF_pieceTest`: pieceTest tl q = true.
  `piecesF_apart`: the ranges of key places of the pieces of call q lie pairwise apart.
  `piecesF_apartTest`: apartTest tl q = true.
How they are proved. piecesF refuses unless t2BL gives one block or two, so placeZ is run on one
piece or two. The order in which placeZ takes two pieces is one of two, and in either the piece
taken first has no smaller range than the other. So the list of placed pieces can be written out
(`piecesF_pieceOK_lay_one`, `piecesF_pieceOK_lay_two`), and the clauses follow by arithmetic. Each
block of t2BL has a power of two as its number of rows (`piecesF_pieceOK_blocks`).

What is not claimed. Nothing is said of a record that is made otherwise than by piecesF, or of one
that a later routine has turned. piecesF returns a record whose field heard is none, and
Fo.tail_four_law (OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean) asks for a record that has heard the
lookup: that the later routines keep the fields which the tests read is not shown here. Where tau
is a power of two a call has one piece, and the two statements on ranges apart say nothing.
Nothing is claimed on soundness, completeness or hiding.
-/
import OnBytes.Model.Tail
import OnBytes.Slice.ProgCodes
import OnBytes.Tie.Pv.Lookup.Digits.PortLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoTailNums
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PiecesF
open OnBytes OnBytes.Model OnBytes.DgP Cb.LdLkp Cb.Lkp

/-! ## The blocks of t2BL -/

/-- Each block that the loop of t2BL makes has a power of two as its number of rows. -/
theorem piecesF_pieceOK_loop (R : ℕ) :
    ∀ (fuel r0 : ℕ), ∀ x ∈ t2BLLoop R fuel r0, ∃ e, x.2 = 2 ^ e
  | 0, _, x, hx => by cases hx
  | fuel + 1, r0, x, hx => by
    rw [t2BLLoop] at hx
    split_ifs at hx with h
    · rcases List.mem_cons.1 hx with e | hx'
      · exact ⟨Nat.log2 (R - r0), by rw [e]⟩
      · exact piecesF_pieceOK_loop R fuel _ x hx'
    · cases hx

/-- So has each block that t2BL returns. -/
theorem piecesF_pieceOK_blocks {R : ℕ} {bz : Array (ℕ × ℕ)} (h : t2BL R = .ok bz) (i : ℕ)
    (hi : i < bz.size) : ∃ e, (bz.getD i (0, 0)).2 = 2 ^ e := by
  unfold t2BL at h
  have hb : (t2BLLoop R (Nat.log2 R + 1) 0).toArray = bz := by
    by_cases c : ((t2BLLoop R (Nat.log2 R + 1) 0).any fun x => x.1 % x.2 != 0) = true
    · simp only [c, if_true] at h
      cases h
    · simp only [c] at h
      exact Except.ok.inj h
  have e : bz.getD i (0, 0) = bz[i] := by
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [e]
  clear e h
  subst hb
  exact piecesF_pieceOK_loop R (Nat.log2 R + 1) 0 _ (Array.getElem_mem_toList hi)

/-! ## The order in which placeZ takes one piece or two -/

/-- One number: the list is that number. -/
theorem piecesF_pieceOK_order_one (key : ℕ → ℕ) : byFallingKey 1 key = [0] := by
  have hm := Ends.mem_byFallingKey key 1
  have hp := Ends.pairwise_byFallingKey key 1
  generalize byFallingKey 1 key = l at hm hp
  match l, hm, hp with
  | [], hm, _ => exact absurd ((hm 0).2 Nat.one_pos) (by simp)
  | [a], hm, _ =>
    have ha : a < 1 := (hm a).1 (by simp)
    rw [Nat.lt_one_iff.1 ha]
  | a :: b :: _, hm, hp =>
    have ha : a < 1 := (hm a).1 (by simp)
    have hb : b < 1 := (hm b).1 (by simp)
    have hab := (List.pairwise_cons.1 hp).1 b (by simp)
    rw [Nat.lt_one_iff.1 ha, Nat.lt_one_iff.1 hb] at hab
    exact absurd hab (Ends.fallsBefore_irrefl key 0)

/-- Two numbers: the one that stands first has no smaller key than the other. -/
theorem piecesF_pieceOK_order_two (key : ℕ → ℕ) :
    (key 1 ≤ key 0 ∧ byFallingKey 2 key = [0, 1]) ∨
      (key 0 ≤ key 1 ∧ byFallingKey 2 key = [1, 0]) := by
  have hm := Ends.mem_byFallingKey key 2
  have hp := Ends.pairwise_byFallingKey key 2
  generalize byFallingKey 2 key = l at hm hp
  have ne : ∀ {a b : ℕ}, Ends.fallsBefore key a b → a ≠ b := fun h e =>
    Ends.fallsBefore_irrefl key _ (e ▸ h)
  match l, hm, hp with
  | [], hm, _ => exact absurd ((hm 0).2 Nat.two_pos) (by simp)
  | [a], hm, _ =>
    have h0 : 0 = a := by simpa using (hm 0).2 Nat.two_pos
    have h1 : 1 = a := by simpa using (hm 1).2 Nat.one_lt_two
    omega
  | [a, b], hm, hp =>
    have ha : a < 2 := (hm a).1 (by simp)
    have hb : b < 2 := (hm b).1 (by simp)
    have hab := (List.pairwise_cons.1 hp).1 b (by simp)
    have hne := ne hab
    have hc : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
    rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine Or.inl ⟨?_, rfl⟩
      unfold Ends.fallsBefore at hab
      omega
    · refine Or.inr ⟨?_, rfl⟩
      unfold Ends.fallsBefore at hab
      omega
  | a :: b :: c :: _, hm, hp =>
    have ha : a < 2 := (hm a).1 (by simp)
    have hb : b < 2 := (hm b).1 (by simp)
    have hc : c < 2 := (hm c).1 (by simp)
    have hab := ne ((List.pairwise_cons.1 hp).1 b (by simp))
    have hac := ne ((List.pairwise_cons.1 hp).1 c (by simp))
    have hbc := ne ((List.pairwise_cons.1 (List.pairwise_cons.1 hp).2).1 c (by simp))
    omega

/-! ## placeZ, written out -/

/-- A piece with the three numbers that placeZ computes from its rows and columns. -/
def piecesF_pieceOK_size (p : Piece) : Piece :=
  { p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp }

/-- The fold of placeZ: the placed pieces, and the first key place behind them. -/
def piecesF_pieceOK_lay (sized : Array Piece) : Array Piece × ℕ :=
  (byFallingKey sized.size fun i => ((sized[i]?).map (·.b)).getD 0).foldl
    (fun (s : Array Piece × ℕ) i =>
      (s.1.modify i (fun p => { p with off := s.2 }), s.2 + 2 ^ ((sized[i]?).map (·.b)).getD 0))
    (sized, 0)

/-- The pieces of placeZ's call. -/
theorem piecesF_pieceOK_pieces (ps : Array Piece) (name : String) (k lid : ℕ) :
    (placeZ ps name k lid).pieces = (piecesF_pieceOK_lay (ps.map piecesF_pieceOK_size)).1 := rfl

/-- The number of bits of placeZ's call. -/
theorem piecesF_pieceOK_bits (ps : Array Piece) (name : String) (k lid : ℕ) :
    (placeZ ps name k lid).call.n =
      max 10 (clog2 (piecesF_pieceOK_lay (ps.map piecesF_pieceOK_size)).2) := rfl

/-- One piece is placed at 0. -/
theorem piecesF_pieceOK_lay_one (s : Piece) :
    piecesF_pieceOK_lay #[s] = (#[{ s with off := 0 }], 0 + 2 ^ s.b) := by
  unfold piecesF_pieceOK_lay
  rw [show (#[s] : Array Piece).size = 1 from rfl, piecesF_pieceOK_order_one]
  rfl

/-- Of two pieces one is placed at 0 and the other behind it, and the first has no smaller range. -/
theorem piecesF_pieceOK_lay_two (s t : Piece) :
    (t.b ≤ s.b ∧ piecesF_pieceOK_lay #[s, t] =
        (#[{ s with off := 0 }, { t with off := 0 + 2 ^ s.b }], 0 + 2 ^ s.b + 2 ^ t.b)) ∨
      (s.b ≤ t.b ∧ piecesF_pieceOK_lay #[s, t] =
        (#[{ s with off := 0 + 2 ^ t.b }, { t with off := 0 }], 0 + 2 ^ t.b + 2 ^ s.b)) := by
  unfold piecesF_pieceOK_lay
  rw [show (#[s, t] : Array Piece).size = 2 from rfl]
  rcases piecesF_pieceOK_order_two fun i => (((#[s, t] : Array Piece)[i]?).map (·.b)).getD 0 with
    ⟨h, e⟩ | ⟨h, e⟩
  · exact Or.inl ⟨h, by rw [e]; rfl⟩
  · exact Or.inr ⟨h, by rw [e]; rfl⟩

/-- p' is the piece p as placeZ sizes it, placed at a multiple of its range, inside 2^n places. -/
def piecesF_pieceOK_Laid (n : ℕ) (p p' : Piece) : Prop :=
  ∃ off, p' = { piecesF_pieceOK_size p with off := off } ∧
    2 ^ (piecesF_pieceOK_size p).b ∣ off ∧ off + 2 ^ (piecesF_pieceOK_size p).b ≤ 2 ^ n

/-- What lies below the first free place lies below 2^n, n being the call's number of bits. -/
theorem piecesF_pieceOK_below {x o : ℕ} (h : x ≤ o) : x ≤ 2 ^ max 10 (clog2 o) :=
  Nat.le_trans h (Nat.le_trans (Ends.le_two_pow_ceilLog2 o)
    (Nat.pow_le_pow_right Nat.two_pos (Nat.le_max_right _ _)))

/-- placeZ on one piece or two: each placed piece is one of the given, sized and placed lawfully,
and the ranges of key places lie pairwise apart. -/
theorem piecesF_pieceOK_placeZ (ps : Array Piece) (name : String) (k lid : ℕ)
    (hs : ps.size = 1 ∨ ps.size = 2) :
    (∀ p' ∈ (placeZ ps name k lid).pieces.toList, ∃ p ∈ ps.toList,
      piecesF_pieceOK_Laid (placeZ ps name k lid).call.n p p') ∧
    (placeZ ps name k lid).pieces.toList.Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off := by
  rw [piecesF_pieceOK_pieces, piecesF_pieceOK_bits]
  obtain ⟨l⟩ := ps
  match l, hs with
  | [], hs => simp at hs
  | [s], _ =>
    rw [show (#[s] : Array Piece).map piecesF_pieceOK_size = #[piecesF_pieceOK_size s] by simp,
      piecesF_pieceOK_lay_one]
    refine ⟨fun p' hp' => ?_, List.pairwise_singleton _ _⟩
    rw [List.mem_singleton.1 hp']
    exact ⟨s, List.mem_singleton.2 rfl, 0, rfl, Nat.dvd_zero _,
      piecesF_pieceOK_below (Nat.le_refl _)⟩
  | [s, t], _ =>
    rw [show (#[s, t] : Array Piece).map piecesF_pieceOK_size =
      #[piecesF_pieceOK_size s, piecesF_pieceOK_size t] by simp]
    rcases piecesF_pieceOK_lay_two (piecesF_pieceOK_size s) (piecesF_pieceOK_size t) with
      ⟨h, e⟩ | ⟨h, e⟩
    · rw [e]
      refine ⟨fun p' hp' => ?_, List.pairwise_pair.2 (Or.inl (Nat.le_refl _))⟩
      rcases List.mem_pair.1 hp' with e' | e'
      · rw [e']
        exact ⟨s, by simp, 0, rfl, Nat.dvd_zero _, piecesF_pieceOK_below (Nat.le_add_right _ _)⟩
      · rw [e']
        exact ⟨t, by simp, _, rfl, by rw [Nat.zero_add]; exact Nat.pow_dvd_pow 2 h,
          piecesF_pieceOK_below (Nat.le_refl _)⟩
    · rw [e]
      refine ⟨fun p' hp' => ?_, List.pairwise_pair.2 (Or.inr (Nat.le_refl _))⟩
      rcases List.mem_pair.1 hp' with e' | e'
      · rw [e']
        exact ⟨s, by simp, _, rfl, by rw [Nat.zero_add]; exact Nat.pow_dvd_pow 2 h,
          piecesF_pieceOK_below (Nat.le_refl _)⟩
      · rw [e']
        exact ⟨t, by simp, 0, rfl, Nat.dvd_zero _, piecesF_pieceOK_below (Nat.le_add_right _ _)⟩
  | _ :: _ :: _ :: _, hs => simp at hs

/-- A piece that is laid so meets PieceOK, if the given piece lies in ZZ, begins at the call's first
column and has a power of two as its number of rows. -/
theorem piecesF_pieceOK_of_laid {tl : HTailF2} {q n : ℕ} {p p' : Piece}
    (h : piecesF_pieceOK_Laid n p p') (ht : p.tree = tl.ix.ZZ) (hc : p.c0 = q * tl.mz)
    (hr : ∃ e, p.Rp = 2 ^ e) : PieceOK tl q n p' := by
  obtain ⟨off, rfl, hd, hf⟩ := h
  obtain ⟨e, he⟩ := hr
  have hw : clog2 (2 ^ clog2 p.Cp) = clog2 p.Cp := Slice.ceilLog2_two_pow _
  refine ⟨ht, hc, Ends.le_two_pow_ceilLog2 p.Cp, ?_, ?_, ?_, ?_, hd, hf⟩
  · show 2 ^ clog2 p.Cp = 2 ^ clog2 (2 ^ clog2 p.Cp)
    rw [hw]
  · show p.Rp = 2 ^ clog2 p.Rp
    rw [he]
    exact congrArg (2 ^ ·) (Slice.ceilLog2_two_pow e).symm
  · show clog2 p.Rp + clog2 p.Cp = clog2 p.Rp + clog2 (2 ^ clog2 p.Cp)
    rw [hw]
  · exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (Nat.le_trans (Nat.le_add_left _ _) hf)

/-! ## The walk through piecesF -/

/-- The pieces that piecesF hands to placeZ for one call: one for each block. -/
def piecesF_pieceOK_given (tl : HTailF2) (bz : Array (ℕ × ℕ)) (row : ℕ → ℕ) (c0 : ℕ) :
    Array Piece :=
  (Array.range bz.size).map fun i =>
    { tree := tl.ix.ZZ, row := row i, r0 := (bz.getD i (0, 0)).1, Rp := (bz.getD i (0, 0)).2,
      c0 := c0, Cp := tl.mz }

/-- What piecesF's value holds of the blocks and of the two runs of placeZ. -/
theorem piecesF_pieceOK_walk {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    ∃ bz, t2BL tl0.tau = .ok bz ∧ (bz.size = 1 ∨ bz.size = 2) ∧ tl.ix = tl0.ix ∧ tl.mz = tl0.mz ∧
      tl.z1 = placeZ (piecesF_pieceOK_given tl0 bz (fun i => i) 0) "R10z" t2D0 tl0.lidb ∧
      tl.z2 = placeZ (piecesF_pieceOK_given tl0 bz (fun i => bz.size + i) tl0.mz) "R8d" t2D1
        tl0.lidb := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, hb, h⟩ := Ends.ok_of_bind h
  obtain ⟨hc, h⟩ := Ends.ok_of_jp h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨f9, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, _, h⟩ := Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  refine ⟨bz, hb, ?_, rfl, rfl, rfl, rfl⟩
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Array.isEmpty_iff_size_eq_zero] at hc
  omega

/-- The same for call q. -/
theorem piecesF_pieceOK_call {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) (q : ℕ) (hq : q < 2) :
    ∃ bz row name k, t2BL tl0.tau = .ok bz ∧ (bz.size = 1 ∨ bz.size = 2) ∧ tl.ix = tl0.ix ∧
      tl.mz = tl0.mz ∧
      tl.zOf q = placeZ (piecesF_pieceOK_given tl0 bz row (q * tl0.mz)) name k tl0.lidb := by
  obtain ⟨bz, hb, hs, hi, hm, e1, e2⟩ := piecesF_pieceOK_walk h
  rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
  · exact ⟨bz, _, _, _, hb, hs, hi, hm, by rw [Nat.zero_mul]; exact e1⟩
  · exact ⟨bz, _, _, _, hb, hs, hi, hm, by rw [Nat.one_mul]; exact e2⟩

/-- There are as many given pieces as blocks. -/
theorem piecesF_pieceOK_given_size (tl : HTailF2) (bz : Array (ℕ × ℕ)) (row : ℕ → ℕ) (c0 : ℕ) :
    (piecesF_pieceOK_given tl bz row c0).size = bz.size := by
  unfold piecesF_pieceOK_given
  rw [Array.size_map, Array.size_range]

/-! ## The four statements -/

/-- Where piecesF returns tl, each piece of either call meets PieceOK at the call's own number of
bits. -/
theorem piecesF_pieceOK :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl →
    ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p := by
  intro tl0 tl h q hq p hp
  obtain ⟨bz, row, name, k, hb, hs, hi, hm, hz⟩ := piecesF_pieceOK_call h q hq
  unfold piecesL at hp
  rw [hz] at hp ⊢
  obtain ⟨p0, hp0, hl⟩ := (piecesF_pieceOK_placeZ _ name k tl0.lidb
    (by rw [piecesF_pieceOK_given_size]; exact hs)).1 p hp
  unfold piecesF_pieceOK_given at hp0
  rw [Array.toList_map, Array.toList_range] at hp0
  obtain ⟨i, hir, rfl⟩ := List.mem_map.1 hp0
  exact piecesF_pieceOK_of_laid hl (congrArg (·.ZZ) hi.symm) (by rw [hm])
    (piecesF_pieceOK_blocks hb i (List.mem_range.1 hir))

/-- Where piecesF returns tl, either call passes pieceTest. -/
theorem piecesF_pieceTest :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl → ∀ q < 2, pieceTest tl q = true := by
  intro tl0 tl e q hq
  refine List.all_eq_true.2 fun p hp => ?_
  have H := piecesF_pieceOK tl0 tl e q hq p hp
  simp only [pieceTest1, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨H.tree, H.c0⟩, H.le⟩, H.pw⟩, H.rp⟩, H.b⟩, H.bn⟩,
    Nat.mod_eq_zero_of_dvd H.dvd⟩, H.fit⟩

/-- Where piecesF returns tl, the ranges of key places of the pieces of either call lie pairwise
apart. -/
theorem piecesF_apart :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl →
    ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off := by
  intro tl0 tl h q hq
  obtain ⟨bz, row, name, k, _, hs, _, _, hz⟩ := piecesF_pieceOK_call h q hq
  unfold piecesL
  rw [hz]
  exact (piecesF_pieceOK_placeZ _ name k tl0.lidb
    (by rw [piecesF_pieceOK_given_size]; exact hs)).2

/-- Where piecesF returns tl, either call passes apartTest. -/
theorem piecesF_apartTest :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl → ∀ q < 2, apartTest tl q = true :=
  fun tl0 tl e q hq => decide_eq_true (piecesF_apart tl0 tl e q hq)

end Fo.PiecesF
