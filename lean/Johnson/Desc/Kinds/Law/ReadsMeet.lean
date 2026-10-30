-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReadsMeet.lean: "A SENT READ's ENTRY IS K6's READ IN TRUTH", TABLE BY TABLE, IN TWO GENERAL LAWS, off the library's own sentences on the tables of reads (Johnson/Road/HeadReads.lean: SumShort, SumLong), AND THE VERIFIER's TABLES OF WEIGHTS READ AS K6's: STATED AND PROVED.
cellsH (adrOf h L b) μ (Johnson/Desc/First/Look/K3CallerHead.lean) reads the entries off the tuple of messages. What is here is general in the integers
and the entries, and fits any record of cells.
  short_meets · long_meets   a table that is SumShort | SumLong on entries cell, integers cz whose images the entries are, weights that read as K6's: its entry e is worth rd of K6's read in truth (readAt | readAtN's own sums) at cz, entry e.
  readAt_short | _long · readAtN_short | _long   what the two laws end in IS readAt | readAtN (rfl).
  wt_eqN · rd_eq_eqN · eqTab_reads   the verifier's table of equality weights (eqTab) reads, entry for entry, as K6's eq.
  longPhi_reads · longPhi_cut   a long table's weights at a point zl ++ zt, and at any point Z of ls + lt coordinates cut in two, read as eq · eq.
  intB · intB_small | _cast | _unique   THE integer of size below B whose image in the field x is; 0 where there is none; there is at most one (B ≤ 2^62).
WHAT IT DOES NOT SAY. That any table IS SumShort | SumLong (Johnson/Road/HeadReads.lean's TrueH wants Holds for every record; Law/TieReads.lean draws that from the smallness test's tie). Which feature a value's limb is. That the run's points are K6's letters. No chance in it.

-/
import Mathlib
import Johnson.Road.HeadReads
import Johnson.Desc.Kinds.Law.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Reading World)
open OnBytes.Road.Hd (SumShort SumLong Starts Valid rdW)
open Norm (lt ls d lPd S2 T)

/-- THE integer of size below B whose image in the field x is; 0 where there is none. -/
noncomputable def intB (B : Nat) (x : K) : Int :=
  open Classical in
  if h : ∃ z : Int, z.natAbs < B ∧ ((z : Int) : K) = x then Classical.choose h else 0

namespace Came

theorem intB_small (B : Nat) (hB : 0 < B) (x : K) : (intB B x).natAbs < B := by
  unfold intB
  split
  · rename_i h
    exact (Classical.choose_spec h).1
  · simpa using hB

theorem intB_cast {B : Nat} {x : K} (h : ∃ z : Int, z.natAbs < B ∧ ((z : Int) : K) = x) :
    ((intB B x : Int) : K) = x := by
  unfold intB
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

/-- There is at most one. -/
theorem intB_unique {B : Nat} (hB : B ≤ 2 ^ 62) {x : K} {z : Int} (hz : z.natAbs < B)
    (hx : ((z : Int) : K) = x) : intB B x = z := by
  have h : ∃ z : Int, z.natAbs < B ∧ ((z : Int) : K) = x := ⟨z, hz, hx⟩
  have h1 := intB_cast h
  have h2 := intB_small B (Nat.lt_of_le_of_lt (Nat.zero_le _) hz) x
  refine int_eq_of_cast_eq (h1.trans hx.symm) ?_
  have a1 : |intB B x| < 2 ^ 62 := by
    rw [Int.abs_eq_natAbs]
    have : (intB B x).natAbs < 2 ^ 62 := Nat.lt_of_lt_of_le h2 hB
    exact_mod_cast this
  have a2 : |z| < 2 ^ 62 := by
    rw [Int.abs_eq_natAbs]
    have : z.natAbs < 2 ^ 62 := Nat.lt_of_lt_of_le hz hB
    exact_mod_cast this
  calc |intB B x - z| ≤ |intB B x| + |z| := abs_sub _ _
    _ < 2 ^ 62 + 2 ^ 62 := add_lt_add a1 a2
    _ = 2 ^ 63 := by norm_num

variable [Sizes]

/-- **A short table's entry is K6's short read in truth.** cz: K6's integers; cell: the entries. -/
theorem short_meets {R : OnBytes.Model.Head.Run} {K3 : Nat} {nm : String} {phi : Array E}
    {W : World K} {cell : Nat → Nat → K} {cz : Nat → Nat → Int}
    (hcz : ∀ e i, ((cz e i : Int) : K) = cell e i) (g : Nat → E) (hT : R.h.T = T)
    (hg : ∀ i, i < T → rd (phi.getD i zeroE) = rd (g i))
    (h : SumShort Reading.gl W R K3 nm phi cell) :
    ∀ tb, Starts R nm tb → ∀ e, Valid R tb e →
      rdW W R.iU3 K3 (tb + e) = rd (sumTo T fun i => g i * ofInt (cz e i)) := by
  intro tb hs e hv
  rw [h tb hs e hv, hT, rd_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rd_mul, rd_ofInt, hcz, ← hg i (Finset.mem_range.1 hi)]
  rfl

/-- **A long table's entry is K6's long read in truth.** -/
theorem long_meets {R : OnBytes.Model.Head.Run} {K3 : Nat} {nm : String} {phi : Array E}
    {W : World K} {cell : Nat → Nat → K} {cz : Nat → Nat → Int}
    (hcz : ∀ e i, ((cz e i : Int) : K) = cell e i) (f g : Nat → E) (hT : R.h.T = T)
    (hS : R.h.S2 = S2)
    (hfg : ∀ r i, r < S2 → i < T → rd (phi.getD (r * T + i) zeroE) = rd (f r) * rd (g i))
    (h : SumLong Reading.gl W R K3 nm phi cell) :
    ∀ tb, Starts R nm tb → ∀ e, Valid R tb e →
      rdW W R.iU3 K3 (tb + e)
        = rd (sumTo S2 fun j => sumTo T fun i => f j * g i * ofInt (cz (S2 * e + j) i)) := by
  intro tb hs e hv
  rw [h tb hs e hv, hT, hS, rd_sumTo]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [rd_mul, rd_mul, rd_ofInt, hcz, ← hfg r i (Finset.mem_range.1 hr) (Finset.mem_range.1 hi),
    Nat.mul_comm e S2]
  rfl

/-! ## The weights: the verifier's tables of equality weights read as K6's -/

/-- The product of factors (Law/Corner.lean: wt) is the library's equality weight (Blocks/Basic.lean: eqN). -/
theorem wt_eqN (i : Nat) : ∀ (l : List K) (off : Nat) (a : Nat → K),
    (∀ t, t < l.length → a (off + t) = l.getD t 0) → wt l i = Blocks.eqN l.length off a i
  | [], _, _, _ => by simp [wt, Blocks.eqN]
  | x :: xs, off, a, h => by
    have ih := wt_eqN i xs (off + 1) a fun t ht => by
      have := h (t + 1) (by simp only [List.length_cons]; omega)
      rw [List.getD_cons_succ] at this
      rw [← this]
      congr 1
      omega
    have h0 : a (off + 0) = x := by
      have := h 0 (by simp)
      simpa using this
    unfold Blocks.eqN at ih ⊢
    rw [List.length_cons, Finset.prod_range_succ', wt, ih, mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun t ht => ?_
      have e1 : xs.length + 1 - 1 - (t + 1) = xs.length - 1 - t := by omega
      have e2 : off + (t + 1) = off + 1 + t := by omega
      rw [e1, e2]
    · have e1 : xs.length + 1 - 1 - 0 = xs.length := by omega
      rw [e1, h0]

/-- K6's equality weight reads as the library's. -/
theorem rd_eq_eqN (z : Point) (i : Nat) (hi : i < 2 ^ z.size) :
    rd (eq z i) = Blocks.eqN z.size 0 (OnBytes.Road.pt Reading.gl z) i := by
  rw [rd_eq, if_pos hi]
  have h := wt_eqN i (z.toList.map rd) 0 (OnBytes.Road.pt Reading.gl z) fun t ht => by
    rw [List.length_map, Array.length_toList] at ht
    unfold OnBytes.Road.pt
    simp [Array.getD, ht, List.getD_eq_getElem?_getD]
    rfl
  rw [List.length_map, Array.length_toList] at h
  exact h

/-- **Entry i of the verifier's table of equality weights reads as K6's eq z i.** -/
theorem eqTab_reads (z : Point) (i : Nat) (hi : i < 2 ^ z.size) :
    rd ((OnBytes.Model.eqTab z).getD i zeroE) = rd (eq z i) := by
  rw [rd_eq_eqN z i hi]
  exact OnBytes.Road.eqTab_value Reading.gl z i hi

/-- **A long table's weights at the point zl ++ zt read as K6's.** -/
theorem longPhi_reads (zl zt : Point) {r i : Nat} (hr : r < 2 ^ zl.size) (hi : i < 2 ^ zt.size) :
    rd ((OnBytes.Model.longPhi (zl ++ zt) zl.size zt.size).getD (r * 2 ^ zt.size + i) zeroE)
      = rd (eq zl r) * rd (eq zt i) := by
  rw [rd_eq_eqN zl r hr, rd_eq_eqN zt i hi]
  refine (OnBytes.Road.longPhi_value Reading.gl (Z := zl ++ zt) (ls := zl.size) (lt := zt.size)
    (by simp) hr hi).trans ?_
  congr 1
  · refine OnBytes.Road.eqN_congr' _ 0 (fun j hj => ?_) r
    unfold OnBytes.Road.pt
    rw [Nat.zero_add, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_append_left hj]
  · refine OnBytes.Road.eqN_congr' _ 0 (fun j hj => ?_) i
    unfold OnBytes.Road.pt
    rw [Nat.zero_add, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

/-- **A long table's weights at any point of a + b coordinates, cut in two, read as K6's.** -/
theorem longPhi_cut (Z : Point) (a b : Nat) (hs : Z.size = a + b) {r i : Nat} (hr : r < 2 ^ a)
    (hi : i < 2 ^ b) :
    rd ((OnBytes.Model.longPhi Z a b).getD (r * 2 ^ b + i) zeroE)
      = rd (eq (Z.extract 0 a) r) * rd (eq (Z.extract a (a + b)) i) := by
  have s1 : (Z.extract 0 a).size = a := by
    rw [Array.size_extract]
    omega
  have s2 : (Z.extract a (a + b)).size = b := by
    rw [Array.size_extract]
    omega
  have t1 := OnBytes.Road.eqTab_size (Z.extract 0 a)
  have t2 := OnBytes.Road.eqTab_size (Z.extract a (a + b))
  rw [s1] at t1
  rw [s2] at t2
  unfold OnBytes.Model.longPhi
  have e : r * 2 ^ b + i = r * (OnBytes.Model.eqTab (Z.extract a (a + b))).size + i := by rw [t2]
  rw [e, OnBytes.Road.blockRows_getD _ _ (by rw [t1]; exact hr) (by rw [t2]; exact hi)]
  show rd (_ * _) = _
  rw [rd_mul, eqTab_reads _ _ (by rw [s1]; exact hr), eqTab_reads _ _ (by rw [s2]; exact hi)]

/-- What the two laws above end in IS readAt | readAtN. -/
theorem readAt_short (c : Cells) (m : Matrix) (g : Nat → E) (e : Nat) :
    readAt c (m, .short g) e = sumTo T fun i => g i * ofInt (c.cell m e i) := rfl

theorem readAt_long (c : Cells) (m : Matrix) (f g : Nat → E) (e : Nat) :
    readAt c (m, .long f g) e
      = sumTo S2 fun j => sumTo T fun i => f j * g i * ofInt (c.cell m (S2 * e + j) i) := rfl

theorem readAtN_short (c : NCells) (m : FinalNorm.Matrix) (g : Nat → E) (e : Nat) :
    readAtN c (m, .short g) e = sumTo T fun i => g i * ofInt (c.of m e i) := rfl

theorem readAtN_long (c : NCells) (m : FinalNorm.Matrix) (f g : Nat → E) (e : Nat) :
    readAtN c (m, .long f g) e
      = sumTo S2 fun j => sumTo T fun i => f j * g i * ofInt (c.of m (S2 * e + j) i) := rfl

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.intB_unique
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.short_meets
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.long_meets
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.eqTab_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.longPhi_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.longPhi_cut
