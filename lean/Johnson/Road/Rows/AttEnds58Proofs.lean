-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEnds58Proofs.lean: proofs of statements of Johnson/Road/Rows/AttEnds58.lean.

Proved here: the four statements whose claims read the matrix ah or no table: ScoreStartEnd
(scoreStartEnd), KeyAtIndexEndB (keyAtIndexEndB), BitsEndA (bitsEndA) and BitsEndB (bitsEndB).

The way. Johnson/Road/Rows/AttReadRow.lean values the verifier's form as the library's read rd2
under the table's own weights on the positions. These weights are a table of equality weights of a
point, which reads as the library's equality polynomial (eqTab_value in
Johnson/Road/FormsKeysEq.lean): rd2_pts. The points are cut from the point of a sumcheck:
pt_extract.

claim8_bitsForm: the routine bitsForm of the statement BitsEndA is the loop in the text of claim 8.

Tools: dim_lT, pt_extract, size_cut, rd2_pts, heads_pos, lt_le_16.


-/
import Johnson.Road.Rows.AttEnds58
import Johnson.Road.Rows.AttReadRow
import Cb.Pv.Att.Mean.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork SubM HTailF2 eqTab)
open OnBytes.Attention (Shape Heard sc3A sc3B minusOne)
open OnBytes.Road.Hd (Ok ok_pure ok_bind)
open Inst.Model.AttSeg (Dim rd2 eqT sh mxV ibV rvM6 rvIBP)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A coordinate of a part of a point. -/
theorem pt_extract (ρ : Reading K) (z : Array E) {a b j : ℕ} (hb : b ≤ z.size)
    (hj : a + j < b) : pt ρ (z.extract a b) j = pt ρ z (a + j) := by
  unfold pt
  rw [getD_extract z hb hj]

/-- The length of a part of a point. -/
theorem size_cut (z : Array E) {a b : ℕ} (hb : b ≤ z.size) : (z.extract a b).size = b - a := by
  rw [Array.size_extract]
  omega

/-- If there is a pair, a head of keys and values has a query head. -/
theorem heads_pos {S : Shape} {b : ℕ} (hb : b < S.NP) : 0 < S.HA := by
  rcases Nat.eq_zero_or_pos S.HA with h0 | h0
  · have e : S.NP = 0 := by
      show S.Lam * S.HA = 0
      rw [h0, Nat.mul_zero]
    omega
  · exact h0

/-- A test that the verifier's function shape has made: a position has at most 16 bits. -/
theorem lt_le_16 {cf : Attention.Cfg} {S : Shape} (h : Attention.shape cf = Except.ok S) :
    cf.lt ≤ 16 := by
  unfold Attention.shape at h
  obtain ⟨e1, -⟩ := L5.refuse_ok h
  simp only [Bool.or_eq_false_iff] at e1
  exact Nat.not_lt.mp (of_decide_eq_false e1.1.2)

section
variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}

/-- The library's number of bits of a position is the shape's. -/
theorem dim_lT (A : AttAt ρ W tl K3 M h lid cf fs) : (L5.dimOf h.S).lT = h.S.cf.lt := by
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have N := L5.norm_of_shaped (L5.shaped_of_hid A.shape) (L5.tested_of_shape hS0).1
    (L5.tested_of_shape hS0).2
  exact N.lt.symm

/-- **A read under the verifier's points is the read under the library's.** zg: the point on the
heads; zi: the point whose equality weights are the table's weights on the positions. -/
theorem rd2_pts (A : AttAt ρ W tl K3 M h lid cf fs) {zg zi : Array E} {ug ui : ℕ → K}
    (hi : zi.size = h.S.cf.lt) (hg : ∀ j < h.S.cf.lgk, pt ρ zg j = ug j)
    (hu : ∀ j < h.S.cf.lt, pt ρ zi j = ui j) (arr : ℕ → ℕ → K) :
    rd2 (L5.dimOf h.S) (pt ρ zg) (fun i => ρ.val ((eqTab zi).getD i zeroE)) arr =
      rd2 (L5.dimOf h.S) ug (eqT (L5.dimOf h.S) ui) arr := by
  have hlT := dim_lT A
  unfold rd2 eqT
  refine sum_congr rfl fun g _ => sum_congr rfl fun i hi' => ?_
  have h1 : Blocks.eqN (L5.dimOf h.S).lg 0 (pt ρ zg) g = Blocks.eqN (L5.dimOf h.S).lg 0 ug g :=
    eqN_agree (fun k hk => by rw [Nat.zero_add]; exact hg k hk) g
  have hi2 : i < 2 ^ zi.size := by
    rw [hi, ← hlT, ← Dim.T_eq]
    exact mem_range.mp hi'
  have h2 : ρ.val ((eqTab zi).getD i zeroE) = Blocks.eqN (L5.dimOf h.S).lT 0 ui i := by
    rw [eqTab_value ρ zi i hi2, hi, hlT]
    exact eqN_agree (fun k hk => by rw [Nat.zero_add]; exact hu k hk) i
  show Blocks.eqN (L5.dimOf h.S).lg 0 (pt ρ zg) g * ρ.val ((eqTab zi).getD i zeroE) * arr g i = _
  rw [h1, h2]

end

/-! ## The score at the index: its start -/

/-- **ScoreStartEnd holds.** -/
theorem scoreStartEnd : ScoreStartEnd := by
  intro K _ ρ W tl K3 M h F lid cf fs p b m G c c1 A hc htg hti hb hpg hpi Tb hrun hval
  obtain ⟨-, -, e⟩ := readMaximum_rd2 A hc Tb (Nat.le_of_eq htg.symm)
    (Nat.mod_lt b (heads_pos hb)) (ok_of_yields hrun)
  rw [Nat.div_add_mod'] at e
  rw [Aff.value_sub, Aff.value_slot, e, sub_eq_zero] at hval
  rw [hval]
  exact rd2_pts A hti hpg hpi _

/-! ## The key at the index: the bits -/

/-- **KeyAtIndexEndB holds.** -/
theorem keyAtIndexEndB : KeyAtIndexEndB := by
  intro K _ ρ W tl K3 M h F lid cf fs b k bit G c c1 A hc hr hb _ Tb hrun hval
  have hlT := dim_lT A
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.pi h.S).size = h.S.cf.lt := by
    show (h.x.scd.r.extract (h.S.cf.lt + h.S.cf.lgk) (2 * h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  obtain ⟨-, -, e⟩ := readIndexBit_rd2 A hc Tb (Nat.le_of_eq s1.symm)
    (Nat.mod_lt b (heads_pos hb)) (ok_of_yields hrun)
  rw [Nat.div_add_mod'] at e
  rw [Aff.value_sub, Aff.value_slot, e, sub_eq_zero] at hval
  rw [hval]
  refine rd2_pts A s2 (fun j hj => ?_) (fun j hj => ?_) _
  · show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ h.x.scd.r ((L5.dimOf h.S).lT + j)
    rw [hlT]
    exact pt_extract ρ _ (by omega) (by omega)
  · show pt ρ (h.x.scd.r.extract (h.S.cf.lt + h.S.cf.lgk) (2 * h.S.cf.lt + h.S.cf.lgk)) j =
      pt ρ h.x.scd.r ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    rw [hlT]
    exact pt_extract ρ _ (by omega) (by omega)

/-! ## The bits of the index -/

/-- The text of claim 8, with bitsForm in the place of the loop that makes the form on the first end
value: the two are the same routine. -/
theorem claim8_bitsForm (h : Heard) :
    Attention.claim8 h = (do
      SubM.lin h.x.scH.rowU
      for b in List.range h.S.NP do
        SubM.lin (sc3B h.x.scH b - sc3A h.x.scH b + Aff.ofConst oneE)
        let f ← bitsForm h b
        SubM.lin f) := rfl

/-- **BitsEndB holds.** -/
theorem bitsEndB : BitsEndB := by
  intro K _ ρ W h b hval
  rw [Aff.value_add, Aff.value_sub, Aff.value_ofConst, ρ.one] at hval
  have e1 : (sc3B h.x.scH b).value ρ W = W.slot (h.x.scH.sEnd + (2 * b + 1)) :=
    Aff.value_slot ρ W _
  have e2 : (sc3A h.x.scH b).value ρ W = W.slot (h.x.scH.sEnd + 2 * b) := Aff.value_slot ρ W _
  rw [e1, e2] at hval
  linear_combination hval

/-- **BitsEndA holds.** -/
theorem bitsEndA : BitsEndA := by
  intro K _ ρ W tl K3 M h F lid cf fs b f G c c1 A hc hr hb Tb hrun hval
  have hlT := dim_lT A
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have h16 : h.S.cf.lt ≤ 16 := by
    rw [(L5.shaped_of_hid A.shape).cfg]
    exact lt_le_16 hS0
  have hr' : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4 := hr
  have s1 : (h.x.rg2 h.S).size = h.S.cf.lgk := by
    show (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.ri2 h.S).size = h.S.cf.lt := by
    show (h.x.scH.r.extract 0 h.S.cf.lt).size = _
    rw [size_cut _ (by omega)]
    omega
  have s3 : (h.x.rk h.S).size = 4 := by
    show (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4)).size = _
    rw [size_cut _ (by omega)]
    omega
  have ha := Nat.mod_lt b (heads_pos hb)
  obtain ⟨-, -, -, e⟩ := foldlM_value ρ W F c
    (fun s k => Attention.readIndexBit h h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k >>=
      fun bit => pure (Aff.addMul s bit (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE))))
    (fun k => -(Blocks.eqN 4 0 (sh (pt ρ h.x.scH.r) ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg)) k *
      rd2 (L5.dimOf h.S) (sh (pt ρ h.x.scH.r) (L5.dimOf h.S).lT)
        (eqT (L5.dimOf h.S) (pt ρ h.x.scH.r)) (ibV (cellsK h.S M) k b)))
    (fun _ => True) (List.range h.S.cf.lt)
    (by
      intro k hk s y G1 D1 hy
      have hk' : k < h.S.cf.lt := List.mem_range.mp hk
      rw [ok_bind] at hy
      obtain ⟨bit, F1, C1, h1, h2⟩ := hy
      obtain ⟨a1, a2, a3⟩ := readIndexBit_rd2 A hc Tb (Nat.le_of_eq s1.symm) ha h1
      rw [ok_pure] at h2
      obtain ⟨b1, b2, b3⟩ := h2
      rw [b1, b2, b3]
      refine ⟨a1, a2, trivial, ?_⟩
      rw [Nat.div_add_mod'] at a3
      have w1 : ρ.val ((eqTab (h.x.rk h.S)).getD k zeroE) =
          Blocks.eqN 4 0 (sh (pt ρ h.x.scH.r) ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg)) k := by
        rw [eqTab_value ρ _ k (by rw [s3]; omega), s3]
        refine eqN_agree (fun j hj => ?_) k
        show pt ρ (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4))
          (0 + j) = pt ρ h.x.scH.r ((L5.dimOf h.S).lT + h.S.cf.lgk + (0 + j))
        rw [hlT, Nat.zero_add]
        exact pt_extract ρ _ (by omega) (by omega)
      have w2 : rd2 (L5.dimOf h.S) (pt ρ (h.x.rg2 h.S))
          (fun i => ρ.val ((eqTab (h.x.ri2 h.S)).getD i zeroE)) (ibV (cellsK h.S M) k b) =
          rd2 (L5.dimOf h.S) (sh (pt ρ h.x.scH.r) (L5.dimOf h.S).lT)
            (eqT (L5.dimOf h.S) (pt ρ h.x.scH.r)) (ibV (cellsK h.S M) k b) := by
        refine rd2_pts A s2 (fun j hj => ?_) (fun j hj => ?_) _
        · show pt ρ (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
            pt ρ h.x.scH.r ((L5.dimOf h.S).lT + j)
          rw [hlT]
          exact pt_extract ρ _ (by omega) (by omega)
        · show pt ρ (h.x.scH.r.extract 0 h.S.cf.lt) j = pt ρ h.x.scH.r j
          rw [pt_extract ρ _ (by omega) (by omega), Nat.zero_add]
      have w3 : ρ.val minusOne = -1 := by
        show ρ.val (subE zeroE oneE) = -1
        rw [ρ.sub, ρ.zero, ρ.one, zero_sub]
      rw [Aff.value_addMul, ρ.mul, w3, w1, a3, w2]
      ring)
    (sc3A h.x.scH b) f G c1 (ok_of_yields hrun)
  have e0 : (sc3A h.x.scH b).value ρ W = W.slot (h.x.scH.sEnd + 2 * b) := Aff.value_slot ρ W _
  rw [hval, e0, sum_map_range, ← hlT] at e
  rw [bitCube_ext (L5.dimOf h.S) (cellsK h.S M) 4 (by rw [hlT]; omega) b]
  rw [sum_neg_distrib] at e
  linear_combination -e

end OnBytes.Road.Rows
