-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailLay.lean: how the pieces of a smallness test's two lookup
calls lie, from the success of the Lean verifier's own routine that makes them.

Wherever piecesF (OnBytes/Model/Tail.lean) returns a record, on any argument, the record meets the
fields pc, rows and one of TailOK (OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean): each piece has mz
columns, at most CP; CP * Rp = 2^b; its keys end at or below 2^n of its call; its rows end at or
below tau; every row below tau lies in a piece; two pieces of one call whose rows or keys meet agree
in all that Piece.same reads.

Main names:
  piecesF_tail_lay_loop, piecesF_tail_lay_blocks: the blocks of t2BL are powers of two, lie one
    behind the other, end at or below R, and cover every row below R.
  piecesF_tail_lay_fold, piecesF_tail_lay_place: placeZ keeps each piece but for a, CP, b and off,
    and lays the pieces' ranges of keys pairwise apart, below 2^n.
  piecesF_tail_lay_cut: what the value of piecesF holds of the routine's own steps.
  piecesF_tail_lay_call: the three fields for one call.
  piecesF_tail_lay: the three fields for the record.

What is not claimed. The other fields of TailOK (port, nc, cnt) are not shown here. The record is
the one that piecesF returns, with heard = none; nothing is said of a later record. That TailOK is
the right thing to ask of a record is not shown. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Model.Tail
import OnBytes.Slice.ProgCodes
import OnBytes.Tie.Pv.Lookup.Digits.PortLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoTailNums
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PiecesF
open OnBytes OnBytes.Model OnBytes.DgP Cb.LdLkp Cb.Lkp

/-! ## The blocks -/

/-- The blocks of the loop from r0 on: each is a power of two, begins at or behind r0 and ends at or
below R; each begins where an earlier one has ended, or later; if what is left is below 2^fuel, they
cover every row from r0 up to R. -/
theorem piecesF_tail_lay_loop (R : ℕ) : ∀ (fuel r0 : ℕ),
    (∀ x ∈ t2BLLoop R fuel r0, (∃ a, x.2 = 2 ^ a) ∧ r0 ≤ x.1 ∧ x.1 + x.2 ≤ R) ∧
    (t2BLLoop R fuel r0).Pairwise (fun x y => x.1 + x.2 ≤ y.1) ∧
    (R - r0 < 2 ^ fuel → ∀ u, r0 ≤ u → u < R →
      ∃ x ∈ t2BLLoop R fuel r0, x.1 ≤ u ∧ u < x.1 + x.2)
  | 0, r0 => by
    refine ⟨fun x hx => (by cases hx), List.Pairwise.nil, fun h u h1 h2 => ?_⟩
    rw [pow_zero] at h
    omega
  | fuel + 1, r0 => by
    obtain ⟨ih1, ih2, ih3⟩ := piecesF_tail_lay_loop R fuel (r0 + 2 ^ Nat.log2 (R - r0))
    by_cases hr : r0 < R
    · have e : t2BLLoop R (fuel + 1) r0 =
          (r0, 2 ^ Nat.log2 (R - r0)) :: t2BLLoop R fuel (r0 + 2 ^ Nat.log2 (R - r0)) := by
        simp only [t2BLLoop, if_pos hr]
      have hle : 2 ^ Nat.log2 (R - r0) ≤ R - r0 := Nat.log2_self_le (by omega)
      have hlt : R - r0 < 2 ^ (Nat.log2 (R - r0) + 1) := Nat.lt_log2_self
      rw [e]
      refine ⟨?_, List.pairwise_cons.mpr ⟨fun y hy => (ih1 y hy).2.1, ih2⟩, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · refine ⟨⟨_, rfl⟩, Nat.le_refl _, ?_⟩
          show r0 + 2 ^ Nat.log2 (R - r0) ≤ R
          omega
        · obtain ⟨h1, h2, h3⟩ := ih1 x hx
          exact ⟨h1, by omega, h3⟩
      · intro hf u h1 h2
        by_cases hu : u < r0 + 2 ^ Nat.log2 (R - r0)
        · exact ⟨_, List.mem_cons_self, h1, hu⟩
        · have hl : Nat.log2 (R - r0) < fuel + 1 := (Nat.log2_lt (by omega)).2 hf
          have hp : 2 ^ Nat.log2 (R - r0) ≤ 2 ^ fuel :=
            Nat.pow_le_pow_right (by omega) (by omega)
          rw [pow_succ] at hlt
          obtain ⟨x, hx, hh⟩ := ih3 (by omega) u (by omega) h2
          exact ⟨x, List.mem_cons_of_mem _ hx, hh⟩
    · have e : t2BLLoop R (fuel + 1) r0 = [] := by simp only [t2BLLoop, if_neg hr]
      rw [e]
      exact ⟨fun x hx => (by cases hx), List.Pairwise.nil, fun _ u h1 h2 => by omega⟩

/-- The blocks of t2BL, by their numbers: each is a power of two and ends at or below R; a later one
begins where an earlier one has ended, or later; they cover every row below R. -/
theorem piecesF_tail_lay_blocks {R : ℕ} {bz : Array (ℕ × ℕ)} (h : t2BL R = .ok bz) :
    (∀ i < bz.size, (∃ a, (bz.getD i (0, 0)).2 = 2 ^ a) ∧
      (bz.getD i (0, 0)).1 + (bz.getD i (0, 0)).2 ≤ R) ∧
    (∀ i j, i < j → j < bz.size →
      (bz.getD i (0, 0)).1 + (bz.getD i (0, 0)).2 ≤ (bz.getD j (0, 0)).1) ∧
    (∀ u < R, ∃ i < bz.size,
      (bz.getD i (0, 0)).1 ≤ u ∧ u < (bz.getD i (0, 0)).1 + (bz.getD i (0, 0)).2) := by
  obtain ⟨h1, h2, h3⟩ := piecesF_tail_lay_loop R (Nat.log2 R + 1) 0
  obtain ⟨o, ho⟩ : ∃ o, o = t2BLLoop R (Nat.log2 R + 1) 0 := ⟨_, rfl⟩
  rw [← ho] at h1 h2 h3
  have hz : bz = o.toArray := by
    unfold t2BL at h
    rw [← ho] at h
    by_cases c : (o.any fun x => x.1 % x.2 != 0) = true
    · simp only [c, if_true] at h
      cases h
    · simp only [c] at h
      exact (Except.ok.inj h).symm
  subst hz
  have hg : ∀ i (hi : i < o.length), o.toArray.getD i (0, 0) = o[i] := by
    intro i hi
    simp [Array.getD_eq_getD_getElem?, hi]
  rw [List.size_toArray]
  refine ⟨fun i hi => ?_, fun i j hij hj => ?_, fun u hu => ?_⟩
  · rw [hg i hi]
    exact ⟨(h1 _ (List.getElem_mem hi)).1, (h1 _ (List.getElem_mem hi)).2.2⟩
  · rw [hg i (by omega), hg j hj]
    exact List.pairwise_iff_getElem.mp h2 i j (by omega) hj hij
  · obtain ⟨x, hx, hh⟩ := h3 (by rw [Nat.sub_zero]; exact Nat.lt_log2_self) u (Nat.zero_le _) hu
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i, hi, by rw [hg i hi]; exact hh⟩

/-! ## The placing -/

/-- One step of placeZ's fold: piece number i gets the running sum as its first key, and the sum
grows by 2^(key i). -/
def piecesF_tail_lay_step (key : ℕ → ℕ) (t : Array Piece × ℕ) (i : ℕ) : Array Piece × ℕ :=
  (t.1.modify i (fun p => { p with off := t.2 }), t.2 + 2 ^ key i)

/-- The fold over a list without repeats: the pieces whose numbers are in the list get a first key
each, and no other field or piece is turned; the ranges of keys lie from the start up to the final
sum, pairwise apart. -/
theorem piecesF_tail_lay_fold (key : ℕ → ℕ) : ∀ (L : List ℕ) (arr : Array Piece) (s : ℕ),
    L.Nodup → ∃ o : ℕ → ℕ,
      (∀ i, (L.foldl (piecesF_tail_lay_step key) (arr, s)).1[i]? =
        if i ∈ L then (arr[i]?).map (fun p => { p with off := o i }) else arr[i]?) ∧
      s ≤ (L.foldl (piecesF_tail_lay_step key) (arr, s)).2 ∧
      (∀ i ∈ L, s ≤ o i ∧ o i + 2 ^ key i ≤ (L.foldl (piecesF_tail_lay_step key) (arr, s)).2) ∧
      (∀ i ∈ L, ∀ j ∈ L, i ≠ j → o i + 2 ^ key i ≤ o j ∨ o j + 2 ^ key j ≤ o i)
  | [], arr, s, _ =>
    ⟨fun _ => 0, fun i => (by simp), Nat.le_refl _, fun i hi => (by cases hi),
      fun i hi => (by cases hi)⟩
  | j :: L, arr, s, hnd => by
    obtain ⟨hj, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨o, h1, h2, h3, h4⟩ := piecesF_tail_lay_fold key L
      (arr.modify j fun p => { p with off := s }) (s + 2 ^ key j) hnd'
    have hf : (j :: L).foldl (piecesF_tail_lay_step key) (arr, s) =
        L.foldl (piecesF_tail_lay_step key)
          (arr.modify j fun p => { p with off := s }, s + 2 ^ key j) := rfl
    rw [hf]
    refine ⟨fun i => if i = j then s else o i, fun i => ?_,
      Nat.le_trans (Nat.le_add_right _ _) h2, fun i hi => ?_,
      fun i hi i' hi' hne => ?_⟩
    · rw [h1 i]
      by_cases e : i = j
      · subst e
        rw [if_neg hj, if_pos List.mem_cons_self, Array.getElem?_modify, if_pos rfl]
        simp only [if_true]
      · have hm : (i ∈ j :: L) ↔ i ∈ L := by simp [e]
        rw [Array.getElem?_modify, if_neg (Ne.symm e)]
        simp only [hm, if_neg e]
    · dsimp only
      by_cases e : i = j
      · subst e
        rw [if_pos rfl]
        exact ⟨Nat.le_refl _, h2⟩
      · rw [if_neg e]
        obtain ⟨a, b⟩ := h3 i ((List.mem_cons.mp hi).resolve_left e)
        exact ⟨Nat.le_trans (Nat.le_add_right _ _) a, b⟩
    · dsimp only
      by_cases e : i = j
      · have e' : i' ≠ j := fun x => hne (e.trans x.symm)
        rw [if_pos e, if_neg e', e]
        exact Or.inl (h3 i' ((List.mem_cons.mp hi').resolve_left e')).1
      · by_cases e' : i' = j
        · rw [if_neg e, if_pos e', e']
          exact Or.inr (h3 i ((List.mem_cons.mp hi).resolve_left e)).1
        · rw [if_neg e, if_neg e']
          exact h4 i ((List.mem_cons.mp hi).resolve_left e) i'
            ((List.mem_cons.mp hi').resolve_left e') hne

/-- placeZ: piece number i comes back with a, CP and b from its own numbers of rows and columns and
with a first key o i; its keys end at or below 2^n; the ranges of keys of two pieces lie apart. -/
theorem piecesF_tail_lay_place (pieces : Array Piece) (name : String) (k lid : ℕ) :
    ∃ o : ℕ → ℕ,
      (∀ i : ℕ, (placeZ pieces name k lid).pieces[i]? = (pieces[i]?).map fun (p : Piece) =>
        ({ p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp,
                  off := o i } : Piece)) ∧
      (∀ i p, pieces[i]? = some p →
        o i + 2 ^ (clog2 p.Rp + clog2 p.Cp) ≤ 2 ^ (placeZ pieces name k lid).call.n) ∧
      (∀ i p j p', pieces[i]? = some p → pieces[j]? = some p' → i ≠ j →
        o i + 2 ^ (clog2 p.Rp + clog2 p.Cp) ≤ o j ∨
          o j + 2 ^ (clog2 p'.Rp + clog2 p'.Cp) ≤ o i) := by
  obtain ⟨sized, hsz⟩ : ∃ sized, sized = pieces.map fun p =>
      ({ p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp } : Piece) :=
    ⟨_, rfl⟩
  obtain ⟨key, hkey⟩ : ∃ key : ℕ → ℕ, key = fun i => ((sized[i]?).map (·.b)).getD 0 := ⟨_, rfl⟩
  have hP : (placeZ pieces name k lid).pieces =
      ((byFallingKey sized.size key).foldl (piecesF_tail_lay_step key) (sized, 0)).1 := by
    subst hkey hsz
    rfl
  have hN : (placeZ pieces name k lid).call.n = max 10 (clog2
      ((byFallingKey sized.size key).foldl (piecesF_tail_lay_step key) (sized, 0)).2) := by
    subst hkey hsz
    rfl
  have hnd : (byFallingKey sized.size key).Nodup := by
    refine List.Pairwise.imp ?_ (Ends.pairwise_byFallingKey key sized.size)
    intro a b hab e
    rw [e] at hab
    exact Ends.fallsBefore_irrefl key b hab
  obtain ⟨o, h1, -, h3, h4⟩ := piecesF_tail_lay_fold key _ sized 0 hnd
  have hk : ∀ i p, pieces[i]? = some p →
      i ∈ byFallingKey sized.size key ∧ key i = clog2 p.Rp + clog2 p.Cp := by
    intro i p hp
    have hs : sized[i]? = some
        { p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp } := by
      rw [hsz, Array.getElem?_map, hp, Option.map_some]
    refine ⟨(Ends.mem_byFallingKey key _ i).mpr (Array.getElem?_eq_some_iff.mp hs).1, ?_⟩
    rw [hkey]
    simp only [hs, Option.map_some, Option.getD_some]
  refine ⟨o, fun i => ?_, fun i p hp => ?_, fun i p j p' hp hp' hne => ?_⟩
  · rw [hP, h1 i]
    cases hp : pieces[i]? with
    | none =>
      have hs : sized[i]? = none := by rw [hsz, Array.getElem?_map, hp, Option.map_none]
      rw [hs]
      simp
    | some p =>
      rw [if_pos (hk i p hp).1, hsz, Array.getElem?_map, hp, Option.map_some, Option.map_some,
        Option.map_some]
  · obtain ⟨hm, e⟩ := hk i p hp
    rw [hN, ← e]
    exact (h3 i hm).2.trans ((Ends.le_two_pow_ceilLog2 _).trans
      (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)))
  · obtain ⟨hm, e⟩ := hk i p hp
    obtain ⟨hm', e'⟩ := hk j p' hp'
    rw [← e, ← e']
    exact h4 i hm j hm' hne

/-! ## One call -/

/-- The three fields for a call whose pieces are made one for each block of t2BL, each with mz
columns. -/
theorem piecesF_tail_lay_call {R mz : ℕ} {bz : Array (ℕ × ℕ)} (hb : t2BL R = .ok bz)
    (mk : ℕ → Piece)
    (hmk : ∀ i, (mk i).r0 = (bz.getD i (0, 0)).1 ∧ (mk i).Rp = (bz.getD i (0, 0)).2 ∧
      (mk i).Cp = mz)
    (name : String) (k lid : ℕ) {z : CallZ}
    (hz : z = placeZ ((Array.range bz.size).map mk) name k lid) :
    (∀ p ∈ z.pieces.toList, p.Cp = mz ∧ p.Cp ≤ p.CP ∧ p.CP * p.Rp = 2 ^ p.b ∧
      p.off + 2 ^ p.b ≤ 2 ^ z.call.n ∧ p.r0 + p.Rp ≤ R) ∧
    (∀ u < R, (z.pieces.toList.find? fun p =>
      decide (p.r0 ≤ u) && decide (u < p.r0 + p.Rp)).isSome = true) ∧
    (∀ p ∈ z.pieces.toList, ∀ p' ∈ z.pieces.toList,
      ((p.r0 < p'.r0 + p'.Rp ∧ p'.r0 < p.r0 + p.Rp) ∨
        (p.off < p'.off + 2 ^ p'.b ∧ p'.off < p.off + 2 ^ p.b)) →
      Piece.same p p') := by
  obtain ⟨F1, F2, F3⟩ := piecesF_tail_lay_blocks hb
  obtain ⟨o, A, B, C⟩ := piecesF_tail_lay_place ((Array.range bz.size).map mk) name k lid
  rw [← hz] at A B
  have hget : ∀ i, ((Array.range bz.size).map mk)[i]? =
      if i < bz.size then some (mk i) else none := by
    intro i
    rw [Array.getElem?_map, Array.getElem?_range]
    split <;> rfl
  have hin : ∀ p ∈ z.pieces.toList, ∃ i < bz.size, p.off = o i ∧
      p.r0 = (bz.getD i (0, 0)).1 ∧ p.Rp = (bz.getD i (0, 0)).2 ∧ p.Cp = mz ∧
      p.CP = 2 ^ clog2 mz ∧ p.b = clog2 (bz.getD i (0, 0)).2 + clog2 mz := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    rw [Array.getElem?_toList, A i, hget i] at hi
    by_cases hlt : i < bz.size
    · rw [if_pos hlt, Option.map_some] at hi
      obtain ⟨m1, m2, m3⟩ := hmk i
      have e := (Option.some.inj hi).symm
      subst e
      refine ⟨i, hlt, rfl, m1, m2, m3, ?_, ?_⟩
      · show 2 ^ clog2 (mk i).Cp = _
        rw [m3]
      · show clog2 (mk i).Rp + clog2 (mk i).Cp = _
        rw [m2, m3]
    · rw [if_neg hlt] at hi
      cases hi
  have hkeys : ∀ i < bz.size, o i + 2 ^ (clog2 (bz.getD i (0, 0)).2 + clog2 mz) ≤
      2 ^ z.call.n := by
    intro i hi
    have h := B i (mk i) (by rw [hget i, if_pos hi])
    rw [(hmk i).2.1, (hmk i).2.2] at h
    exact h
  have hapart : ∀ i < bz.size, ∀ j < bz.size, i ≠ j →
      o i + 2 ^ (clog2 (bz.getD i (0, 0)).2 + clog2 mz) ≤ o j ∨
        o j + 2 ^ (clog2 (bz.getD j (0, 0)).2 + clog2 mz) ≤ o i := by
    intro i hi j hj hne
    have h := C i (mk i) j (mk j) (by rw [hget i, if_pos hi]) (by rw [hget j, if_pos hj]) hne
    rw [(hmk i).2.1, (hmk i).2.2, (hmk j).2.1, (hmk j).2.2] at h
    exact h
  refine ⟨fun p hp => ?_, fun u hu => ?_, fun p hp p' hp' hmeet => ?_⟩
  · obtain ⟨i, hi, e1, e2, e3, e4, e5, e6⟩ := hin p hp
    obtain ⟨⟨a, ha⟩, hR⟩ := F1 i hi
    refine ⟨e4, ?_, ?_, ?_, ?_⟩
    · rw [e4, e5]
      exact Ends.le_two_pow_ceilLog2 mz
    · have hc : clog2 (2 ^ a) = a := Slice.ceilLog2_two_pow a
      rw [e5, e3, e6, ha, hc, pow_add, Nat.mul_comm]
    · rw [e1, e6]
      exact hkeys i hi
    · rw [e2, e3]
      exact hR
  · obtain ⟨i, hi, hu1, hu2⟩ := F3 u hu
    rw [List.find?_isSome]
    refine ⟨_, List.mem_iff_getElem?.mpr ⟨i, by
      rw [Array.getElem?_toList, A i, hget i, if_pos hi, Option.map_some]⟩, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [(hmk i).1, (hmk i).2.1]
    exact ⟨hu1, hu2⟩
  · obtain ⟨i, hi, e1, e2, e3, e4, e5, e6⟩ := hin p hp
    obtain ⟨j, hj, f1, f2, f3, f4, f5, f6⟩ := hin p' hp'
    by_cases e : i = j
    · subst e
      exact ⟨e1.trans f1.symm, e2.trans f2.symm, e3.trans f3.symm, e5.trans f5.symm,
        e4.trans f4.symm, e6.trans f6.symm⟩
    · exfalso
      have hk := hapart i hi j hj e
      rw [e1, e2, e3, e6, f1, f2, f3, f6] at hmeet
      rcases Nat.lt_or_gt_of_ne e with hlt | hlt
      · have hr := F2 i j hlt hj
        omega
      · have hr := F2 j i hlt hi
        omega

/-! ## The record -/

/-- What the value of piecesF holds of the routine's own steps: the blocks, the two calls, the shape
of the lookup; tau and mz are kept. -/
theorem piecesF_tail_lay_cut {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    ∃ bz f9 pub, t2BL tl0.tau = .ok bz ∧
      tl.z1 = placeZ ((Array.range bz.size).map fun i =>
        ({ tree := tl0.ix.ZZ, row := i, r0 := (bz.getD i (0, 0)).1, Rp := (bz.getD i (0, 0)).2,
           c0 := 0, Cp := tl0.mz } : Piece)) "R10z" t2D0 tl0.lidb ∧
      tl.z2 = placeZ ((Array.range bz.size).map fun i =>
        ({ tree := tl0.ix.ZZ, row := bz.size + i, r0 := (bz.getD i (0, 0)).1,
           Rp := (bz.getD i (0, 0)).2, c0 := tl0.mz, Cp := tl0.mz } : Piece)) "R8d" t2D1
          tl0.lidb ∧
      Forest.shape #[tl.z1.call, tl.z2.call] tl0.lidb = .ok f9 ∧
      tl.f9 = { f9 with pub := pub } ∧ tl.tau = tl0.tau ∧ tl.mz = tl0.mz := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, hb, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨f9, hs, h⟩ := Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, _, h⟩ := Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨bz, f9, pub, hb, rfl, rfl, hs, rfl, rfl, rfl⟩

/-- The record has two calls, and the shape's number of bits of a call's keys is the call's own. -/
theorem piecesF_tail_lay_n {tl : HTailF2} {f9 : Forest.Shape} {pub : Array ℕ} {lid : ℕ}
    (hs : Forest.shape #[tl.z1.call, tl.z2.call] lid = .ok f9)
    (ef : tl.f9 = { f9 with pub := pub }) :
    tl.f9.NC = 2 ∧ ∀ q < 2, Port.nOf tl.f9 q = (tl.zOf q).call.n := by
  obtain ⟨hc, hN, -⟩ := Cb.Fo.shape_more hs
  have hcs : tl.f9.calls = #[tl.z1.call, tl.z2.call] := by
    rw [ef]
    exact hc
  refine ⟨by rw [ef]; exact hN, fun q hq => ?_⟩
  unfold Port.nOf
  rw [hcs]
  obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  · rfl
  · rfl

/-- Wherever piecesF returns a record, the record meets the fields pc, rows and one of TailOK. -/
theorem piecesF_tail_lay :
  ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl →
    (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, p.Cp = tl.mz ∧ p.Cp ≤ p.CP ∧ p.CP * p.Rp = 2 ^ p.b ∧
      p.off + 2 ^ p.b ≤ 2 ^ Port.nOf tl.f9 q ∧ p.r0 + p.Rp ≤ tl.tau) ∧
    (∀ q < tl.f9.NC, ∀ u < tl.tau, (pieceAt tl q u).isSome = true) ∧
    (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, ∀ p' ∈ piecesL tl q,
      ((p.r0 < p'.r0 + p'.Rp ∧ p'.r0 < p.r0 + p.Rp) ∨
        (p.off < p'.off + 2 ^ p'.b ∧ p'.off < p.off + 2 ^ p.b)) →
      Piece.same p p') := by
  intro tl0 tl h
  obtain ⟨bz, f9, pub, hb, e1, e2, hs, ef, et, em⟩ := piecesF_tail_lay_cut h
  obtain ⟨hNC, hn⟩ := piecesF_tail_lay_n hs ef
  rw [← et] at hb
  rw [← em] at e1 e2
  have K0 := piecesF_tail_lay_call (mz := tl.mz) hb _ (fun _ => ⟨rfl, rfl, rfl⟩) _ _ _ e1
  have K1 := piecesF_tail_lay_call (mz := tl.mz) hb _ (fun _ => ⟨rfl, rfl, rfl⟩) _ _ _ e2
  rw [hNC]
  refine ⟨fun q hq p hp => ?_, fun q hq u hu => ?_, fun q hq => ?_⟩
  · rw [hn q hq]
    obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact K0.1 p hp
    · exact K1.1 p hp
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact K0.2.1 u hu
    · exact K1.2.1 u hu
  · obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
    · exact K0.2.2
    · exact K1.2.2

end Fo.PiecesF
