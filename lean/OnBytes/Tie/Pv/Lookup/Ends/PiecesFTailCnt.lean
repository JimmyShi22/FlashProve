-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lookup/Ends/PiecesFTailCnt.lean: the field cnt of TailOK
(OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean) at every record that HTailF2.piecesF
(OnBytes/Model/Tail.lean), a routine of the Lean verifier under OnBytes/, returns.

The statement: for each of the two lookup calls, the keys of the call's trees are as many as the
call's public padding keys and its mz tau digits together. No refusal of the routine tests this
sum; it follows from how the routine counts.

How it is proved.
 - Forest.pubRun, where it returns, adds its argument count to the counts of the call's own trees
   and to no other tree's (`piecesF_tail_cnt_pubLoop`, `piecesF_tail_cnt_pubRun`).
 - So the three nested loops of piecesF add, for each call, the places behind the columns in each
   row of each piece and the places behind the last piece (`piecesF_tail_cnt_due`,
   `piecesF_tail_cnt_walk`).
 - The blocks of t2BL are powers of two and their lengths sum to tau (`piecesF_tail_cnt_t2BL`).
   placeZ lays one or two pieces one after the other from place 0 on, so these padding places and
   the mz tau cells of the pieces make 2^n (`piecesF_tail_cnt_call`).
 - Under Port.OK the trees that go with a call are its run of 2^iota trees and, for call 0, the
   trees of padding alone, which stand on both sides (`piecesF_tail_cnt_of_sum`).

Main name:
  `piecesF_tail_cnt`: if tl0.piecesF = .ok tl, then the field cnt of TailOK holds of tl.

What is not claimed: that piecesF returns a record at any input; the other fields of TailOK;
anything on a record that is made otherwise or that a later routine has turned (piecesF ends with
heard := none); that TailOK is the right thing to ask of a record; anything on soundness,
completeness or hiding.
-/
import OnBytes.Model.Tail
import OnBytes.Slice.ProgCodes
import OnBytes.Tie.Pv.Lookup.Digits.PortLaws
import OnBytes.Tie.Pv.Lookup.Ends.FoTailNums
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.PiecesF
open OnBytes OnBytes.Model OnBytes.DgP Cb.LdLkp Cb.Lkp

/-! ## Sums of counts over a list of trees -/

/-- The sum of the entries of pub at the indices of a list. -/
def piecesF_tail_cnt_sumOn (L : List ℕ) (pub : Array ℕ) : ℕ := (L.map fun y => pub.getD y 0).sum

/-- Over an array of zeros the sum is 0. -/
theorem piecesF_tail_cnt_sumOn_zero (n : ℕ) :
    ∀ L : List ℕ, piecesF_tail_cnt_sumOn L (Array.replicate n 0) = 0
  | [] => rfl
  | y :: L => by
    have ih := piecesF_tail_cnt_sumOn_zero n L
    unfold piecesF_tail_cnt_sumOn at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split_ifs <;> rfl

/-- Adding t at an index inside the array adds t to the sum as often as the list has the index. -/
theorem piecesF_tail_cnt_sumOn_modify (pub : Array ℕ) {j : ℕ} (hj : j < pub.size) (t : ℕ) :
    ∀ L : List ℕ, piecesF_tail_cnt_sumOn L (pub.modify j (· + t)) =
      piecesF_tail_cnt_sumOn L pub + L.count j * t
  | [] => by simp [piecesF_tail_cnt_sumOn]
  | y :: L => by
    have ih := piecesF_tail_cnt_sumOn_modify pub hj t L
    unfold piecesF_tail_cnt_sumOn at ih ⊢
    have e : (pub.modify j (· + t)).getD y 0 = pub.getD y 0 + if (y == j) = true then t else 0 := by
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
      by_cases h : j = y
      · subst h
        simp [hj]
      · have h' : ¬ y = j := fun e => h e.symm
        simp [h, h']
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ih, List.count_cons, e]
    split_ifs <;> ring

/-! ## Forest.pubLoop and Forest.pubRun -/

/-- The loop of pubRun adds count in all, at trees of the call's run, if the places end inside the
run and the steps suffice. k is how often the list has a tree of the run. -/
theorem piecesF_tail_cnt_pubLoop (L : List ℕ) (dT base i k : ℕ) :
    ∀ (steps : ℕ) (pub : Array ℕ) (first count : ℕ),
      (count = 0 ∨ first + count ≤ (first / 2 ^ dT + steps) * 2 ^ dT) →
      first + count ≤ 2 ^ i * 2 ^ dT →
      (∀ b < 2 ^ i, base + b < pub.size ∧ L.count (base + b) = k) →
      piecesF_tail_cnt_sumOn L (Forest.pubLoop dT base steps pub first count) =
        piecesF_tail_cnt_sumOn L pub + k * count
  | 0, pub, first, count, hf, _, _ => by
    have h0 : count = 0 := by
      rcases hf with h | h
      · exact h
      · have h1 := Nat.div_mul_le_self first (2 ^ dT)
        rw [Nat.add_zero] at h
        omega
    subst h0
    rfl
  | steps + 1, pub, first, count, hf, hle, hb => by
    by_cases h0 : count = 0
    · subst h0
      rw [Forest.pubLoop, if_pos rfl]
      rfl
    · obtain ⟨D, hD⟩ : ∃ D, D = 2 ^ dT := ⟨_, rfl⟩
      have hDpos : 0 < D := by rw [hD]; positivity
      obtain ⟨b, hbd⟩ : ∃ b, b = first / D := ⟨_, rfl⟩
      obtain ⟨take, htd⟩ : ∃ take, take = min count ((b + 1) * D - first) := ⟨_, rfl⟩
      have e : Forest.pubLoop dT base (steps + 1) pub first count =
          Forest.pubLoop dT base steps (pub.modify (base + b) (· + take)) (first + take)
            (count - take) := by
        rw [Forest.pubLoop, if_neg h0, htd, hbd, hD]
      rw [← hD] at hf hle
      rw [← hbd] at hf
      have hf' : first + count ≤ (b + (steps + 1)) * D := by
        rcases hf with h | h
        · exact absurd h h0
        · exact h
      have hlo : b * D ≤ first := by rw [hbd]; exact Nat.div_mul_le_self _ _
      have hhi : first < (b + 1) * D := by
        have h1 := Nat.lt_mul_div_succ first hDpos
        rw [hbd, Nat.mul_comm]
        exact h1
      have hbi : b < 2 ^ i := by
        rw [hbd]
        exact (Nat.div_lt_iff_lt_mul hDpos).2 (by omega)
      have htc : take ≤ count := by rw [htd]; exact Nat.min_le_left _ _
      obtain ⟨hsz, hk⟩ := hb b hbi
      have ih := piecesF_tail_cnt_pubLoop L dT base i k steps (pub.modify (base + b) (· + take))
        (first + take) (count - take) (by
          rw [← hD]
          by_cases hc : count ≤ (b + 1) * D - first
          · left
            rw [htd, Nat.min_eq_left hc, Nat.sub_self]
          · right
            have ht : take = (b + 1) * D - first := by
              rw [htd]
              exact Nat.min_eq_right (by omega)
            have e1 : first + take = (b + 1) * D := by omega
            rw [e1, Nat.mul_div_cancel _ hDpos]
            have e2 : (b + 1 + steps) * D = (b + (steps + 1)) * D := by ring
            omega) (by rw [← hD]; omega) (by rw [Array.size_modify]; exact hb)
      rw [e, ih, piecesF_tail_cnt_sumOn_modify pub hsz take L, hk, Nat.add_assoc, ← Nat.mul_add,
        Nat.add_sub_cancel' htc]

/-- Where pubRun returns, it has added count at trees of the call's run. -/
theorem piecesF_tail_cnt_pubRun (L : List ℕ) (h : Forest.Shape) (q k : ℕ)
    (hb : ∀ b < 2 ^ h.iota.getD q 0,
      h.first.getD q 0 + b < h.NT ∧ L.count (h.first.getD q 0 + b) = k)
    {pub pub' : Array ℕ} {first count : ℕ} (hr : Forest.pubRun h pub q first count = .ok pub') :
    piecesF_tail_cnt_sumOn L pub' = piecesF_tail_cnt_sumOn L pub + k * count := by
  unfold Forest.pubRun at hr
  obtain ⟨c1, hr⟩ := Ends.ok_of_jp hr
  obtain ⟨c2, hr⟩ := Ends.ok_of_jp hr
  have e := (Except.ok.inj hr).symm
  subst e
  have s : pub.size = h.NT := by
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, not_not] at c1
    exact c1.1
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, gt_iff_lt] at c2
  have hle : first + count ≤ 2 ^ h.iota.getD q 0 * 2 ^ h.dT := by
    rw [← pow_add, Nat.add_comm (h.iota.getD q 0)]
    omega
  refine piecesF_tail_cnt_pubLoop L h.dT (h.first.getD q 0) (h.iota.getD q 0) k _ pub first count
    (Or.inr (Nat.le_trans hle (Nat.mul_le_mul_right _
      (Nat.le_trans (Nat.le_succ _) (Nat.le_add_left _ _))))) hle (by rw [s]; exact hb)

/-! ## The blocks of rows -/

/-- The blocks of t2BLLoop are powers of two, and their lengths sum to what was left, if the fuel
suffices. -/
theorem piecesF_tail_cnt_t2BLLoop (R : ℕ) : ∀ (fuel r0 : ℕ), R - r0 < 2 ^ fuel →
    ((t2BLLoop R fuel r0).map (·.2)).sum = R - r0 ∧ ∀ x ∈ t2BLLoop R fuel r0, ∃ a, x.2 = 2 ^ a
  | 0, r0, h => by
    have h0 : R - r0 = 0 := by
      rw [pow_zero] at h
      omega
    rw [h0]
    exact ⟨rfl, fun x hx => by cases hx⟩
  | fuel + 1, r0, h => by
    rw [t2BLLoop]
    by_cases hlt : r0 < R
    · rw [if_pos hlt]
      have hne : R - r0 ≠ 0 := by omega
      have h1 : 2 ^ Nat.log2 (R - r0) ≤ R - r0 := Nat.log2_self_le hne
      have h2 : R - r0 < 2 ^ (Nat.log2 (R - r0) + 1) := Nat.lt_log2_self
      have h3 : Nat.log2 (R - r0) < fuel + 1 := (Nat.log2_lt hne).2 h
      have h4 : 2 ^ Nat.log2 (R - r0) ≤ 2 ^ fuel := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at h2
      obtain ⟨i1, i2⟩ := piecesF_tail_cnt_t2BLLoop R fuel (r0 + 2 ^ Nat.log2 (R - r0)) (by omega)
      refine ⟨?_, fun x hx => ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        rw [i1]
        omega
      · rcases List.mem_cons.1 hx with e | hx
        · exact ⟨_, by rw [e]⟩
        · exact i2 x hx
    · rw [if_neg hlt]
      exact ⟨by simp; omega, fun x hx => by cases hx⟩

/-- The blocks of t2BL are powers of two, and their lengths sum to the number of rows. -/
theorem piecesF_tail_cnt_t2BL {R : ℕ} {bz : Array (ℕ × ℕ)} (h : t2BL R = .ok bz) :
    (bz.toList.map (·.2)).sum = R ∧ ∀ x ∈ bz.toList, ∃ a, x.2 = 2 ^ a := by
  unfold t2BL at h
  dsimp only at h
  split_ifs at h
  have e := (Except.ok.inj h).symm
  subst e
  exact piecesF_tail_cnt_t2BLLoop R _ 0 Nat.lt_log2_self

/-! ## The two sides of the count, from the sum over the call's trees -/

/-- A sum over the numbers below n in which one member alone counts. -/
theorem piecesF_tail_cnt_sum_one (P : ℕ → Prop) [DecidablePred P] (v : ℕ → ℕ) (c : ℕ) :
    ∀ n, (∀ c' < n, P c' ↔ c' = c) →
      ((List.range n).map fun c' => if P c' then v c' else 0).sum = if c < n then v c else 0
  | 0, _ => rfl
  | n + 1, h => by
    have ih := piecesF_tail_cnt_sum_one P v c n fun c' hc' => h c' (by omega)
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_singleton,
      List.sum_singleton]
    by_cases e : n = c
    · subst e
      rw [if_neg (Nat.lt_irrefl _), if_pos ((h n (by omega)).2 rfl), if_pos (by omega),
        Nat.zero_add]
    · rw [if_neg fun hp => e ((h n (by omega)).1 hp), Nat.add_zero]
      by_cases hc : c < n
      · rw [if_pos hc, if_pos (by omega)]
      · rw [if_neg hc, if_neg (by omega)]

/-- The padding of call c's own row: the sum over its trees, and for call 0 the empty trees. -/
theorem piecesF_tail_cnt_padCnt (h : Port.Sh) (hOK : Port.OK h) {c : ℕ} (hc : c < h.NC) :
    padCnt (padsP h) (c + 2 ^ h.cK * Port.t0Of h c) =
      piecesF_tail_cnt_sumOn ((List.range h.NT).filter fun y => Port.co h y = c) h.pub +
        if c = 0 then h.emptyKeys else 0 := by
  obtain ⟨_, h2, _⟩ := hOK
  unfold padCnt padsP
  rw [List.map_map]
  have e := piecesF_tail_cnt_sum_one
    (fun c' => c' + 2 ^ h.cK * Port.t0Of h c' = c + 2 ^ h.cK * Port.t0Of h c)
    (fun c' => piecesF_tail_cnt_sumOn ((List.range h.NT).filter fun y => Port.co h y = c') h.pub +
        if c' = 0 then h.emptyKeys else 0) c h.NC (fun c' hc' => ⟨fun e => by
      have e1 := congrArg (· % 2 ^ h.cK) e
      simp only [Nat.add_mul_mod_self_left] at e1
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e1, fun e => by rw [e]⟩)
  rw [if_pos hc] at e
  exact e

/-- The trees of call c are the run of 2^iota trees from its first tree on. -/
theorem piecesF_tail_cnt_run (h : Port.Sh) (hOK : Port.OK h) {c : ℕ} (hc : c < h.NC) :
    Nat.count (fun y => Port.co h y = c) h.NT = 2 ^ Port.io h c := by
  obtain ⟨_, _, _, h4, _, h6⟩ := hOK
  obtain ⟨_, _, hb⟩ := h6 c hc
  rw [Nat.count_eq_card_filter_range]
  have e : (Finset.range h.NT).filter (fun y => Port.co h y = c) =
      Finset.Ico (Port.fst h c) (Port.fst h c + 2 ^ Port.io h c) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hy, rfl⟩
      exact (h4 y hy).2
    · rintro ⟨h1, h2⟩
      obtain ⟨b1, b2, _⟩ := hb (y - Port.fst h c) (by omega)
      rw [Nat.add_sub_cancel' h1] at b1 b2
      exact ⟨b1, b2⟩
  rw [e, Nat.card_Ico, Nat.add_sub_cancel_left]

/-- The numbers of trees that go with call c: its run, and for call 0 the empty trees. -/
theorem piecesF_tail_cnt_fK (h : Port.Sh) (hOK : Port.OK h) {c : ℕ} (hc : c < h.NC) :
    Nat.count (fun y => Port.fK h y = c) (2 ^ h.rK) =
      2 ^ Port.io h c + if c = 0 then 2 ^ h.rK - h.NT else 0 := by
  have h3 : h.NT ≤ 2 ^ h.rK := hOK.2.2.1
  have e0 : 2 ^ h.rK = h.NT + (2 ^ h.rK - h.NT) := by omega
  have e1 : Nat.count (fun y => Port.fK h y = c) h.NT =
      Nat.count (fun y => Port.co h y = c) h.NT := by
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    refine congrArg Finset.card (Finset.filter_congr fun y hy => ?_)
    have hy' : y < h.NT := Finset.mem_range.1 hy
    unfold Port.fK
    rw [Nat.mod_eq_of_lt (by omega), if_pos hy']
  have e2 : Nat.count (fun k => Port.fK h (h.NT + k) = c) (2 ^ h.rK - h.NT) =
      if c = 0 then 2 ^ h.rK - h.NT else 0 := by
    rw [Nat.count_eq_card_filter_range]
    have e3 : (Finset.range (2 ^ h.rK - h.NT)).filter (fun k => Port.fK h (h.NT + k) = c) =
        (Finset.range (2 ^ h.rK - h.NT)).filter fun _ => 0 = c := by
      refine Finset.filter_congr fun k hk => ?_
      have hk' : k < 2 ^ h.rK - h.NT := Finset.mem_range.1 hk
      unfold Port.fK
      rw [Nat.mod_eq_of_lt (by omega), if_neg (by omega)]
    rw [e3]
    by_cases h0 : c = 0
    · subst h0
      simp
    · rw [if_neg h0, Finset.filter_false_of_mem fun _ _ e => h0 e.symm, Finset.card_empty]
  conv_lhs => rw [e0]
  rw [Nat.count_add, e1, e2, piecesF_tail_cnt_run h hOK hc]

/-- The count of the statement, from: the padding of the call's trees and m make 2^n keys. -/
theorem piecesF_tail_cnt_of_sum (h : Port.Sh) (hOK : Port.OK h) {c : ℕ} (hc : c < h.NC) (m : ℕ)
    (hS : piecesF_tail_cnt_sumOn ((List.range h.NT).filter fun y => Port.co h y = c) h.pub + m =
      2 ^ Port.nOf h c) :
    2 ^ h.dT * Nat.count (fun y => Port.fK h y = c) (2 ^ h.rK) =
      padCnt (padsP h) (c + 2 ^ h.cK * Port.t0Of h c) + m := by
  rw [piecesF_tail_cnt_fK h hOK hc, piecesF_tail_cnt_padCnt h hOK hc]
  have hn : Port.nOf h c = Port.io h c + h.dT := (hOK.2.2.2.2.2 c hc).2.1
  rw [hn, pow_add] at hS
  unfold Forest.Shape.emptyKeys
  split_ifs
  · rw [Nat.mul_add, Nat.mul_comm (2 ^ h.dT) (2 ^ Port.io h c), ← hS,
      Nat.mul_comm (2 ^ h.dT) (2 ^ h.rK - h.NT)]
    omega
  · rw [Nat.add_zero, Nat.add_zero, Nat.mul_comm, ← hS]

/-! ## placeZ on one or two pieces -/

/-- What the loops of piecesF hand to pubRun for a call, in all: in each row of a piece the places
behind its columns, and the places behind the last piece. -/
def piecesF_tail_cnt_due (z : CallZ) : ℕ :=
  (z.pieces.toList.map fun p => p.Rp * (p.CP - p.Cp)).sum +
    (2 ^ z.call.n - z.pieces.toList.foldl (fun s p => max s (p.off + 2 ^ p.b)) 0)

/-- A piece with its sizes, as placeZ makes it before it places it. -/
def piecesF_tail_cnt_size1 (p : Piece) : Piece :=
  { p with a := clog2 p.Rp, CP := 2 ^ clog2 p.Cp, b := clog2 p.Rp + clog2 p.Cp }

/-- The pieces with their sizes. -/
def piecesF_tail_cnt_sized (pcs : Array Piece) : Array Piece := pcs.map piecesF_tail_cnt_size1

/-- The fold of placeZ that places the pieces in a given order. -/
def piecesF_tail_cnt_laid (sz : Array Piece) (ord : List ℕ) : Array Piece × ℕ :=
  ord.foldl (fun (s : Array Piece × ℕ) i =>
      (s.1.modify i (fun p => { p with off := s.2 }), s.2 + 2 ^ ((sz[i]?).map (·.b)).getD 0))
    (sz, 0)

/-- The pieces and the number of key bits of placeZ, in these words. -/
theorem piecesF_tail_cnt_placeZ (pcs : Array Piece) (name : String) (k lid : ℕ) :
    (placeZ pcs name k lid).pieces = (piecesF_tail_cnt_laid (piecesF_tail_cnt_sized pcs)
      (byFallingKey (piecesF_tail_cnt_sized pcs).size
        fun i => (((piecesF_tail_cnt_sized pcs)[i]?).map (·.b)).getD 0)).1 ∧
    (placeZ pcs name k lid).call.n = max 10 (clog2 (piecesF_tail_cnt_laid
      (piecesF_tail_cnt_sized pcs) (byFallingKey (piecesF_tail_cnt_sized pcs).size
        fun i => (((piecesF_tail_cnt_sized pcs)[i]?).map (·.b)).getD 0)).2) := ⟨rfl, rfl⟩

/-- byFallingKey lists the numbers below n, each once. -/
theorem piecesF_tail_cnt_order (key : ℕ → ℕ) (n : ℕ) :
    (byFallingKey n key).Perm (List.range n) := by
  have nd : (byFallingKey n key).Nodup :=
    (Ends.pairwise_byFallingKey key n).imp fun {a b} h e => by
      subst e
      exact Ends.fallsBefore_irrefl key _ h
  exact (List.perm_ext_iff_of_nodup nd List.nodup_range).2 fun c => by
    rw [Ends.mem_byFallingKey, List.mem_range]

/-- The order of one number. -/
theorem piecesF_tail_cnt_order1 (key : ℕ → ℕ) : byFallingKey 1 key = [0] :=
  List.perm_singleton.1 (piecesF_tail_cnt_order key 1)

/-- The two orders of two numbers. -/
theorem piecesF_tail_cnt_order2 (key : ℕ → ℕ) :
    byFallingKey 2 key = [0, 1] ∨ byFallingKey 2 key = [1, 0] := by
  have p := piecesF_tail_cnt_order key 2
  obtain ⟨a, b, e⟩ := List.length_eq_two.1 (p.length_eq.trans List.length_range)
  rw [e] at p ⊢
  have ha : a < 2 := List.mem_range.1 (p.subset (by simp))
  have hb : b < 2 := List.mem_range.1 (p.subset (by simp))
  have nd : [a, b].Nodup := p.nodup_iff.2 List.nodup_range
  have hne : a ≠ b := by
    intro e
    subst e
    simp at nd
  have hc : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- One piece is placed at 0. -/
theorem piecesF_tail_cnt_laid1 (G : Piece) :
    (piecesF_tail_cnt_laid #[G] [0]).1.toList = [{ G with off := 0 }] ∧
      (piecesF_tail_cnt_laid #[G] [0]).2 = 0 + 2 ^ G.b := ⟨rfl, rfl⟩

/-- Two pieces, the first one first. -/
theorem piecesF_tail_cnt_laid01 (G H : Piece) :
    (piecesF_tail_cnt_laid #[G, H] [0, 1]).1.toList =
        [{ G with off := 0 }, { H with off := 0 + 2 ^ G.b }] ∧
      (piecesF_tail_cnt_laid #[G, H] [0, 1]).2 = 0 + 2 ^ G.b + 2 ^ H.b := ⟨rfl, rfl⟩

/-- Two pieces, the second one first. -/
theorem piecesF_tail_cnt_laid10 (G H : Piece) :
    (piecesF_tail_cnt_laid #[G, H] [1, 0]).1.toList =
        [{ G with off := 0 + 2 ^ H.b }, { H with off := 0 }] ∧
      (piecesF_tail_cnt_laid #[G, H] [1, 0]).2 = 0 + 2 ^ H.b + 2 ^ G.b := ⟨rfl, rfl⟩

/-- 2^n has room for what placeZ has placed. -/
theorem piecesF_tail_cnt_room (off : ℕ) : off ≤ 2 ^ max 10 (clog2 off) :=
  Nat.le_trans (Ends.le_two_pow_ceilLog2 off)
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_right _ _))

/-- A call of one piece whose range is its rows times its columns rounded up. -/
theorem piecesF_tail_cnt_due1 (z : CallZ) (G : Piece)
    (hp : z.pieces = (piecesF_tail_cnt_laid #[G] [0]).1)
    (hn : z.call.n = max 10 (clog2 (piecesF_tail_cnt_laid #[G] [0]).2))
    (hG : G.Rp * (G.CP - G.Cp) + G.Rp * G.Cp = 2 ^ G.b) :
    piecesF_tail_cnt_due z + G.Rp * G.Cp = 2 ^ z.call.n := by
  obtain ⟨e1, e2⟩ := piecesF_tail_cnt_laid1 G
  unfold piecesF_tail_cnt_due
  rw [hn, hp, e1, e2]
  have hr := piecesF_tail_cnt_room (0 + 2 ^ G.b)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldl_cons,
    List.foldl_nil]
  omega

/-- A call of two such pieces. -/
theorem piecesF_tail_cnt_due2 (z : CallZ) (G H : Piece) (ord : List ℕ)
    (ho : ord = [0, 1] ∨ ord = [1, 0])
    (hp : z.pieces = (piecesF_tail_cnt_laid #[G, H] ord).1)
    (hn : z.call.n = max 10 (clog2 (piecesF_tail_cnt_laid #[G, H] ord).2))
    (hG : G.Rp * (G.CP - G.Cp) + G.Rp * G.Cp = 2 ^ G.b)
    (hH : H.Rp * (H.CP - H.Cp) + H.Rp * H.Cp = 2 ^ H.b) :
    piecesF_tail_cnt_due z + (G.Rp * G.Cp + H.Rp * H.Cp) = 2 ^ z.call.n := by
  unfold piecesF_tail_cnt_due
  rcases ho with rfl | rfl
  · obtain ⟨e1, e2⟩ := piecesF_tail_cnt_laid01 G H
    rw [hn, hp, e1, e2]
    have hr := piecesF_tail_cnt_room (0 + 2 ^ G.b + 2 ^ H.b)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldl_cons,
      List.foldl_nil]
    omega
  · obtain ⟨e1, e2⟩ := piecesF_tail_cnt_laid10 G H
    rw [hn, hp, e1, e2]
    have hr := piecesF_tail_cnt_room (0 + 2 ^ H.b + 2 ^ G.b)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.foldl_cons,
      List.foldl_nil]
    omega

/-- The rounded-up logarithm of a power of two is the exponent. -/
theorem piecesF_tail_cnt_clog2 (a : ℕ) : clog2 (2 ^ a) = a := OnBytes.Slice.ceilLog2_two_pow a

/-- A piece whose number of rows is a power of two gets a range of rows times columns rounded up. -/
theorem piecesF_tail_cnt_range (R C a : ℕ) (h : R = 2 ^ a) :
    R * (2 ^ clog2 C - C) + R * C = 2 ^ (clog2 R + clog2 C) := by
  rw [← Nat.mul_add, Nat.sub_add_cancel (Ends.le_two_pow_ceilLog2 C), h, piecesF_tail_cnt_clog2,
    pow_add]

/-- The call that placeZ makes of one piece for each of one or two blocks: its padding places and
the cells of its pieces are its 2^n key places. -/
theorem piecesF_tail_cnt_call (bz : Array (ℕ × ℕ)) (mz tau : ℕ)
    (hsz : bz.size = 1 ∨ bz.size = 2) (hsum : (bz.toList.map (·.2)).sum = tau)
    (hpow : ∀ x ∈ bz.toList, ∃ a, x.2 = 2 ^ a) (f : ℕ → ℕ × ℕ → Piece)
    (hf : ∀ i x, (f i x).Rp = x.2 ∧ (f i x).Cp = mz) (name : String) (k lid : ℕ) :
    piecesF_tail_cnt_due (placeZ ((Array.range bz.size).map fun i => f i (bz.getD i (0, 0)))
        name k lid) + mz * tau =
      2 ^ (placeZ ((Array.range bz.size).map fun i => f i (bz.getD i (0, 0)))
        name k lid).call.n := by
  obtain ⟨l⟩ := bz
  rcases hsz with hsz | hsz
  · obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hsz
    have ep : ((Array.range (Array.mk [x]).size).map fun i => f i ((Array.mk [x]).getD i (0, 0))) =
        #[f 0 x] := by
      apply Array.ext'
      simp [List.range_succ]
    rw [ep]
    obtain ⟨e1, e2⟩ := piecesF_tail_cnt_placeZ #[f 0 x] name k lid
    have es : piecesF_tail_cnt_sized #[f 0 x] = #[piecesF_tail_cnt_size1 (f 0 x)] := by
      simp [piecesF_tail_cnt_sized]
    rw [es, show (#[piecesF_tail_cnt_size1 (f 0 x)] : Array Piece).size = 1 from rfl,
      piecesF_tail_cnt_order1] at e1 e2
    obtain ⟨a, ha⟩ := hpow x (by simp)
    have hd := piecesF_tail_cnt_due1 _ _ e1 e2
      (piecesF_tail_cnt_range (f 0 x).Rp (f 0 x).Cp a ((hf 0 x).1.trans ha))
    have ht : tau = x.2 := by simpa using hsum.symm
    rw [← hd, ht]
    show _ + mz * x.2 = _ + (f 0 x).Rp * (f 0 x).Cp
    rw [(hf 0 x).1, (hf 0 x).2, Nat.mul_comm]
  · obtain ⟨x, y, rfl⟩ := List.length_eq_two.1 hsz
    have ep : ((Array.range (Array.mk [x, y]).size).map
        fun i => f i ((Array.mk [x, y]).getD i (0, 0))) = #[f 0 x, f 1 y] := by
      apply Array.ext'
      simp [List.range_succ]
    rw [ep]
    obtain ⟨e1, e2⟩ := piecesF_tail_cnt_placeZ #[f 0 x, f 1 y] name k lid
    have es : piecesF_tail_cnt_sized #[f 0 x, f 1 y] =
        #[piecesF_tail_cnt_size1 (f 0 x), piecesF_tail_cnt_size1 (f 1 y)] := by
      simp [piecesF_tail_cnt_sized]
    rw [es, show (#[piecesF_tail_cnt_size1 (f 0 x), piecesF_tail_cnt_size1 (f 1 y)] :
      Array Piece).size = 2 from rfl] at e1 e2
    obtain ⟨a, ha⟩ := hpow x (by simp)
    obtain ⟨b, hb⟩ := hpow y (by simp)
    have hd := piecesF_tail_cnt_due2 _ _ _ _ (piecesF_tail_cnt_order2 _) e1 e2
      (piecesF_tail_cnt_range (f 0 x).Rp (f 0 x).Cp a ((hf 0 x).1.trans ha))
      (piecesF_tail_cnt_range (f 1 y).Rp (f 1 y).Cp b ((hf 1 y).1.trans hb))
    have ht : tau = x.2 + y.2 := by simpa using hsum.symm
    rw [← hd, ht]
    show _ + mz * (x.2 + y.2) = _ + ((f 0 x).Rp * (f 0 x).Cp + (f 1 y).Rp * (f 1 y).Cp)
    rw [(hf 0 x).1, (hf 0 x).2, (hf 1 y).1, (hf 1 y).2]
    ring

/-! ## The walk through piecesF -/

/-- The piece that piecesF makes of the block x for a call: row is its virtual row, c0 the call's
first column, mz the call's number of columns. -/
def piecesF_tail_cnt_piece (tree c0 mz row : ℕ) (x : ℕ × ℕ) : Piece :=
  { tree := tree, row := row, r0 := x.1, Rp := x.2, c0 := c0, Cp := mz }

/-- What the record that piecesF returns holds of the routine's steps: the blocks, the two calls,
the shape, and what the loops have added to the counts over any list L of trees. k q is how often L
has a tree of call q's run. -/
theorem piecesF_tail_cnt_walk {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    ∃ bz : Array (ℕ × ℕ), t2BL tl.tau = .ok bz ∧ (bz.size = 1 ∨ bz.size = 2) ∧
      tl'.tau = tl.tau ∧ tl'.mz = tl.mz ∧
      tl'.z1 = placeZ ((Array.range bz.size).map fun i =>
        piecesF_tail_cnt_piece tl.ix.ZZ 0 tl.mz i (bz.getD i (0, 0))) "R10z" t2D0 tl.lidb ∧
      tl'.z2 = placeZ ((Array.range bz.size).map fun i =>
        piecesF_tail_cnt_piece tl.ix.ZZ tl.mz tl.mz (bz.size + i) (bz.getD i (0, 0)))
          "R8d" t2D1 tl.lidb ∧
      Port.OK tl'.f9 ∧ tl'.f9.calls = #[tl'.z1.call, tl'.z2.call] ∧ tl'.f9.NC = 2 ∧
      ∀ (L : List ℕ) (k : ℕ → ℕ),
        (∀ q ∈ [0, 1], ∀ b < 2 ^ tl'.f9.iota.getD q 0, tl'.f9.first.getD q 0 + b < tl'.f9.NT ∧
          L.count (tl'.f9.first.getD q 0 + b) = k q) →
        piecesF_tail_cnt_sumOn L tl'.f9.pub =
          k 0 * piecesF_tail_cnt_due tl'.z1 + k 1 * piecesF_tail_cnt_due tl'.z2 := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, hbz, h1⟩ := Ends.ok_of_bind h
  clear h
  obtain ⟨hsz, h2⟩ := Ends.ok_of_jp h1
  clear h1
  obtain ⟨-, h3⟩ := Ends.ok_of_jp h2
  clear h2
  obtain ⟨f9, hs, h4⟩ := Ends.ok_of_bind h3
  clear h3
  obtain ⟨pub, hl, h5⟩ := Ends.ok_of_bind h4
  clear h4
  obtain ⟨u, hp, h⟩ := Ends.ok_of_bind h5
  clear h5
  generalize hz1 : placeZ _ _ t2D0 _ = z1 at hs hl h
  generalize hz2 : placeZ _ _ t2D1 _ = z2 at hs hl h
  have e := (Except.ok.inj h).symm
  subst e
  clear h
  obtain ⟨m1, m2, -⟩ := Cb.Fo.shape_more hs
  refine ⟨bz, hbz, ?_, rfl, rfl, hz1.symm, hz2.symm, Cb.Fo.ok_portOK (Cb.Fo.shape_ok hs hp), m1, m2,
    fun L k hb => ?_⟩
  · simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero, decide_eq_true_eq, not_or] at hsz
    omega
  clear hz1 hz2 hs hp hbz hsz m1 m2
  have K : piecesF_tail_cnt_sumOn L pub = ([0, 1].map fun q =>
      k q * piecesF_tail_cnt_due (if (q == 0) = true then z1 else z2)).sum :=
    Ends.forIn_keeps _ [0, 1]
    (fun pre (s : Array ℕ) => piecesF_tail_cnt_sumOn L s =
      (pre.map fun q => k q * piecesF_tail_cnt_due (if (q == 0) = true then z1 else z2)).sum)
    (fun pre a rest e s s' hI hs => by
      clear hl
      have ha : a ∈ [0, 1] := by rw [e]; simp
      obtain ⟨r, hmid, hs1⟩ := Ends.ok_of_bind hs
      clear hs
      obtain ⟨pub1, stop1⟩ := r
      obtain ⟨pub2, hrun, hs2⟩ := Ends.ok_of_bind hs1
      clear hs1
      refine ⟨pub2, (Except.ok.inj hs2).symm, ?_⟩
      clear hs2
      dsimp only at hI ⊢
      rw [List.map_append, List.sum_append, ← hI, List.map_singleton, List.sum_singleton]
      generalize (if (a == 0) = true then z1 else z2) = c at hmid hrun ⊢
      rw [← Array.forIn_toList] at hmid
      have M : piecesF_tail_cnt_sumOn L pub1 = piecesF_tail_cnt_sumOn L s +
            k a * (c.pieces.toList.map fun p => p.Rp * (p.CP - p.Cp)).sum ∧
          stop1 = c.pieces.toList.foldl (fun s p => max s (p.off + 2 ^ p.b)) 0 :=
        Ends.forIn_keeps _ c.pieces.toList
        (fun pre' (st : MProd (Array ℕ) ℕ) => piecesF_tail_cnt_sumOn L st.1 =
            piecesF_tail_cnt_sumOn L s + k a * (pre'.map fun p => p.Rp * (p.CP - p.Cp)).sum ∧
          st.2 = pre'.foldl (fun s p => max s (p.off + 2 ^ p.b)) 0)
        (fun pre' p _ _ st st' hI' hst => by
          clear hmid hrun
          obtain ⟨pb, sp⟩ := st
          obtain ⟨i1, i2⟩ := hI'
          dsimp only at i1 i2 hst
          by_cases hc : p.Cp < p.CP
          · rw [if_pos hc] at hst
            obtain ⟨pb1, hrows, hst1⟩ := Ends.ok_of_bind hst
            clear hst
            refine ⟨⟨pb1, max sp (p.off + 2 ^ p.b)⟩, (Except.ok.inj hst1).symm, ?_, ?_⟩
            · clear hst1
              have R : piecesF_tail_cnt_sumOn L pb1 = piecesF_tail_cnt_sumOn L pb +
                  k a * ((List.range p.Rp).length * (p.CP - p.Cp)) :=
                Ends.forIn_keeps _ (List.range p.Rp)
                (fun pre'' (t : Array ℕ) => piecesF_tail_cnt_sumOn L t =
                  piecesF_tail_cnt_sumOn L pb + k a * (pre''.length * (p.CP - p.Cp)))
                (fun pre'' rr _ _ t t' hI'' ht => by
                  clear hrows
                  obtain ⟨t1, hr1, ht1⟩ := Ends.ok_of_bind ht
                  refine ⟨t1, (Except.ok.inj ht1).symm, ?_⟩
                  dsimp only at hI'' ⊢
                  rw [piecesF_tail_cnt_pubRun L f9 a (k a) (hb a ha) hr1, hI'', List.length_append,
                    List.length_singleton]
                  ring)
                (List.range p.Rp) [] _ _ rfl (by simp) hrows
              dsimp only
              rw [R, i1, List.length_range, List.map_append, List.sum_append, List.map_singleton,
                List.sum_singleton]
              ring
            · dsimp only
              rw [List.foldl_append, ← i2]
              rfl
          · rw [if_neg hc] at hst
            refine ⟨⟨pb, max sp (p.off + 2 ^ p.b)⟩, (Except.ok.inj hst).symm, ?_, ?_⟩
            · dsimp only
              rw [i1, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
                Nat.sub_eq_zero_of_le (Nat.le_of_not_lt hc), Nat.mul_zero, Nat.add_zero]
            · dsimp only
              rw [List.foldl_append, ← i2]
              rfl)
        c.pieces.toList [] _ _ rfl ⟨by simp, rfl⟩ hmid
      obtain ⟨n1, n2⟩ := M
      rw [piecesF_tail_cnt_pubRun L f9 a (k a) (hb a ha) hrun, n1]
      unfold piecesF_tail_cnt_due
      rw [← n2]
      ring)
    [0, 1] [] _ _ rfl (piecesF_tail_cnt_sumOn_zero _ L) hl
  rw [show piecesF_tail_cnt_sumOn L _ = _ from K]
  show k 0 * piecesF_tail_cnt_due z1 + (k 1 * piecesF_tail_cnt_due z2 + 0) = _
  rw [Nat.add_zero]

/-! ## The count -/

/-- Where piecesF returns a record, the keys of each call's trees are the call's padding keys and
its mz tau digits. -/
theorem piecesF_tail_cnt :
    ∀ (tl0 tl : HTailF2), tl0.piecesF = .ok tl →
      ∀ c < tl.f9.NC, 2 ^ tl.f9.dT * Nat.count (fun y => Port.fK tl.f9 y = c) (2 ^ tl.f9.rK) =
        padCnt (padsP tl.f9) ((portQ tl).zRow c) + tl.mz * tl.tau := by
  intro tl0 tl h c hc
  obtain ⟨bz, hbz, hsz, et, em, ez1, ez2, hOK, hcalls, hNC, hloops⟩ := piecesF_tail_cnt_walk h
  obtain ⟨hsum, hpow⟩ := piecesF_tail_cnt_t2BL hbz
  have d1 : piecesF_tail_cnt_due tl.z1 + tl.mz * tl.tau = 2 ^ tl.z1.call.n := by
    rw [ez1, em, et]
    exact piecesF_tail_cnt_call bz tl0.mz tl0.tau hsz hsum hpow
      (fun i x => piecesF_tail_cnt_piece tl0.ix.ZZ 0 tl0.mz i x) (fun _ _ => ⟨rfl, rfl⟩) _ _ _
  have d2 : piecesF_tail_cnt_due tl.z2 + tl.mz * tl.tau = 2 ^ tl.z2.call.n := by
    rw [ez2, em, et]
    exact piecesF_tail_cnt_call bz tl0.mz tl0.tau hsz hsum hpow
      (fun i x => piecesF_tail_cnt_piece tl0.ix.ZZ tl0.mz tl0.mz (bz.size + i) x)
      (fun _ _ => ⟨rfl, rfl⟩) _ _ _
  have n0 : Port.nOf tl.f9 0 = tl.z1.call.n := by
    unfold Port.nOf
    rw [hcalls]
    rfl
  have n1 : Port.nOf tl.f9 1 = tl.z2.call.n := by
    unfold Port.nOf
    rw [hcalls]
    rfl
  have hS := hloops ((List.range tl.f9.NT).filter fun y => Port.co tl.f9 y = c)
    (fun q => if q = c then 1 else 0) (fun q hq b hb => by
      have hq' : q < tl.f9.NC := by
        rw [hNC]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        omega
      obtain ⟨b1, b2, -⟩ := (hOK.2.2.2.2.2 q hq').2.2 b hb
      refine ⟨b1, ?_⟩
      show List.count _ _ = if q = c then 1 else 0
      by_cases e : q = c
      · rw [if_pos e]
        exact List.count_eq_one_of_mem (List.nodup_range.filter _)
          (List.mem_filter.2 ⟨List.mem_range.2 b1, decide_eq_true (b2.trans e)⟩)
      · rw [if_neg e]
        exact List.count_eq_zero_of_not_mem fun hm =>
          e (b2.symm.trans (of_decide_eq_true (List.mem_filter.1 hm).2)))
  refine piecesF_tail_cnt_of_sum tl.f9 hOK hc (tl.mz * tl.tau) ?_
  rw [hS]
  rw [hNC] at hc
  have hc2 : c = 0 ∨ c = 1 := by omega
  rcases hc2 with rfl | rfl
  · rw [n0, ← d1]
    simp
  · rw [n1, ← d2]
    simp

end Fo.PiecesF
