-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttValid.lean

The library's relation of an attention segment reads valid names only, AT ALL SIZES: two integer
traces that agree on the names that are valid at the sizes D meet Inst.Model.AttSeg.RFraw D
together.

The library has this at the reference sizes (Cm/SegAttAgree.lean: keyVec_agree, idnVal_agree, over
Cm/SegAttKeyKit.lean, Cm/SegAttKey.lean, Cm/SegAttKeySum.lean). The lemmas of this file are those
lemmas with the letter D in the place of the reference sizes. Their proofs are the library's, but
for the facts on sizes that the library has there by evaluation; here they are proved for every D.
What the library states for every D already is used as it stands (twoFam_agree, keyVec0 to keyVec3,
the lemmas on places and blocks of Inst/Model/Att/Index.lean, rowSum_eq).

* "AgreeD D t t'": t and t' agree on the names that are valid at D.
* "keyVec_agree", "idnVal_agree": equal key vectors at every index, equal identities at every valid
  name of an identity, over any commutative ring.
* "rfraw_valid": RFraw D tb F t gives RFraw D tb F t'.

It compares the library with itself. It says nothing on tables, bounds or protocols.
-/
import Cm.SegAttAgree
import Inst.Model.Att.AddrFacts

set_option autoImplicit false
set_option linter.unusedSectionVars false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5.V

open Inst.Model Finset
open Inst.Model.AttSeg (Raw Reg)
open Cm.Seg (twoFam_agree keyVec0 keyVec1 keyVec2 keyVec3)

variable {R : Type} [CommRing R] {D : AttSeg.Dim}

/-- Two traces agree on the names that are valid at D. -/
def AgreeD (D : AttSeg.Dim) (t t' : Raw → R) : Prop := ∀ c : Raw, c.Valid D → t c = t' c

/-! ## Indices are in range -/

theorem pos_lt {a r : ℕ} (ha : a < D.nBlk) (hr : r < D.B) : D.B * a + r < D.T := by
  unfold AttSeg.Dim.T
  nlinarith
theorem mI_lt (x : ℕ) : D.mI x < D.B := Nat.mod_lt _ D.B_pos
theorem mJ_lt (x : ℕ) : D.mJ x < D.B := Nat.mod_lt _ D.B_pos
theorem slotM {x : ℕ} (he : ¬ D.EmptyM x) :
    D.colBlk (D.mP x) (D.mS x) < D.rowBlk (D.mP x) (D.mS x) ∧
    D.rowBlk (D.mP x) (D.mS x) < D.nBlk := by
  have h1 : D.mS x < D.nBlk := Nat.mod_lt _ D.nBlk_pos
  have h2 : D.mS x ≠ D.nBlk - 1 := he
  have h := D.blk_of_slot (P := D.mP x) (s := D.mS x) (Nat.mod_lt _ D.hP_pos) (by omega)
  exact ⟨h.1, h.2.1⟩
theorem iM_lt {x : ℕ} (he : ¬ D.EmptyM x) : D.iM x < D.T := pos_lt (slotM he).2 (mI_lt x)
theorem jM_lt {x : ℕ} (he : ¬ D.EmptyM x) : D.jM x < D.T :=
  pos_lt (lt_trans (slotM he).1 (slotM he).2) (mJ_lt x)
theorem iD_lt (x : ℕ) : D.iD x < D.T := pos_lt (Nat.mod_lt _ D.nBlk_pos) (mI_lt x)
theorem jD_lt (x : ℕ) : D.jD x < D.T := pos_lt (Nat.mod_lt _ D.nBlk_pos) (mJ_lt x)
theorem lam_lt {b : ℕ} (hb : b < D.nb) : D.lamOf b < D.nl := AttSeg.AddrFacts.lam_lt D hb
theorem nG_pos : 0 < D.nG := Nat.two_pow_pos _
theorem ch_pos : 0 < D.ch := Nat.two_pow_pos _

theorem attBlk_le {i : ℕ} (hi : i < D.T) : D.B * (i / D.B + 1) ≤ D.T := by
  have h1 : i / D.B < D.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have h2 : D.T = D.B * D.nBlk := Nat.mul_comm _ _
  rw [h2]
  exact Nat.mul_le_mul_left _ h1

/-! ## The keys, written out -/

section Eq
variable (t : Raw → R)

theorem key2M_eq [scl : Scl] (b x : ℕ) :
    AttSeg.key2 D t .M b x =
      (if D.EmptyM x then ((D.cutC : ℤ) : R)
          else
            AttSeg.mxV t b (D.mG x) (D.iM x) -
              ∑ n ∈ range D.ch, AttSeg.qryV t b (D.mG x) (D.iM x) n *
                AttSeg.keyV t (D.lamOf b) (D.mG x) (D.jM x) n) -
        AttSeg.rm t .M b x + 2 ^ 32 * AttSeg.flV t .M b x + 2 ^ 33 * AttSeg.wtV t .M b x := rfl

theorem key2D_eq [scl : Scl] (b x : ℕ) :
    AttSeg.key2 D t .D b x =
      (AttSeg.mxV t b (D.dG x) (D.iD x) -
          ∑ n ∈ range D.ch, AttSeg.qryV t b (D.dG x) (D.iD x) n *
            AttSeg.keyV t (D.lamOf b) (D.dG x) (D.jD x) n +
          if D.MaskedD x then ((AttSeg.Om D : ℤ) : R) else 0) -
        AttSeg.rm t .D b x + 2 ^ 32 * AttSeg.flV t .D b x + 2 ^ 33 * AttSeg.wtV t .D b x := rfl

/-- RE with the accumulator as one sum over positions -/
theorem RE_eq (b h n : ℕ) {i : ℕ} (hi : i < D.T) :
    AttSeg.RE D t b h i n =
      2 * (∑ j ∈ range (D.B * (i / D.B + 1)),
            AttSeg.wtIJ D t b h i j * AttSeg.valV t (D.lamOf b) h j n) +
        AttSeg.denV t b h i - 2 * AttSeg.denV t b h i * AttSeg.outV t b h i n := by
  show 2 * AttSeg.rowSum D t (fun j => AttSeg.valV t (D.lamOf b) h j n) b h i + _ - _ = _
  rw [AttSeg.rowSum_eq D t _ b h hi]

end Eq

/-! ## The values of a trace -/

section Agree
variable {t t' : Raw → R} (H : AgreeD D t t') {ρ : Reg} {b x h i n k lam j : ℕ}
include H
theorem r0_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.r0 t ρ b x = AttSeg.r0 t' ρ b x := by
  unfold AttSeg.r0; rw [H (.c ρ 0 b x) ⟨by norm_num, hb, hx⟩]
theorem r1_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.r1 t ρ b x = AttSeg.r1 t' ρ b x := by
  unfold AttSeg.r1; rw [H (.c ρ 1 b x) ⟨by norm_num, hb, hx⟩]
theorem fl_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.flV t ρ b x = AttSeg.flV t' ρ b x :=
  H (.c ρ 2 b x) ⟨by norm_num, hb, hx⟩
theorem w0_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.w0 t ρ b x = AttSeg.w0 t' ρ b x := by
  unfold AttSeg.w0; rw [H (.c ρ 3 b x) ⟨by norm_num, hb, hx⟩]
theorem w1_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.w1 t ρ b x = AttSeg.w1 t' ρ b x :=
  H (.c ρ 4 b x) ⟨by norm_num, hb, hx⟩
theorem rm_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.rm t ρ b x = AttSeg.rm t' ρ b x := by
  unfold AttSeg.rm; rw [r0_agree H hb hx, r1_agree H hb hx]
theorem wt_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.wtV t ρ b x = AttSeg.wtV t' ρ b x := by
  unfold AttSeg.wtV; rw [w0_agree H hb hx, w1_agree H hb hx]
theorem mx_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) :
    AttSeg.mxV t b h i = AttSeg.mxV t' b h i :=
  sum_congr rfl fun k hk => by rw [H (.mx k b h i) ⟨mem_range.1 hk, hb, hh, hi⟩]
theorem den_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) :
    AttSeg.denV t b h i = AttSeg.denV t' b h i :=
  sum_congr rfl fun k hk => by rw [H (.den k b h i) ⟨mem_range.1 hk, hb, hh, hi⟩]
theorem ib_agree (hk : k < D.lT) (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) :
    AttSeg.ibV t k b h i = AttSeg.ibV t' k b h i :=
  H (.ib k b h i) ⟨hk, hb, hh, hi⟩
theorem qh_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.qhV t b h i n = AttSeg.qhV t' b h i n := by
  unfold AttSeg.qhV; rw [H (.qh b h i n) ⟨hb, hh, hi, hn⟩]
theorem qh'_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.qhV' t b h i n = AttSeg.qhV' t' b h i n := by
  unfold AttSeg.qhV'; rw [H (.qh' b h i n) ⟨hb, hh, hi, hn⟩]
theorem qry_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.qryV t b h i n = AttSeg.qryV t' b h i n :=
  sum_congr rfl fun k hk => by rw [H (.qry k b h i n) ⟨mem_range.1 hk, hb, hh, hi, hn⟩]
theorem out_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.outV t b h i n = AttSeg.outV t' b h i n :=
  sum_congr rfl fun k hk => by rw [H (.out k b h i n) ⟨mem_range.1 hk, hb, hh, hi, hn⟩]
theorem key_agree (hl : lam < D.nl) (hh : h < D.nG) (hj : j < D.T) (hn : n < D.ch) :
    AttSeg.keyV t lam h j n = AttSeg.keyV t' lam h j n :=
  sum_congr rfl fun k hk => by rw [H (.key k lam h j n) ⟨mem_range.1 hk, hl, hh, hj, hn⟩]
theorem val_agree (hl : lam < D.nl) (hh : h < D.nG) (hj : j < D.T) (hn : n < D.ch) :
    AttSeg.valV t lam h j n = AttSeg.valV t' lam h j n :=
  sum_congr rfl fun k hk => by rw [H (.val k lam h j n) ⟨mem_range.1 hk, hl, hh, hj, hn⟩]

/-! ## The parts of the keys -/

theorem attSc_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hj : j < D.T) :
    ∑ n ∈ range D.ch, AttSeg.qryV t b h i n * AttSeg.keyV t (D.lamOf b) h j n =
      ∑ n ∈ range D.ch, AttSeg.qryV t' b h i n * AttSeg.keyV t' (D.lamOf b) h j n :=
  sum_congr rfl fun n hn => by
    rw [qry_agree H hb hh hi (mem_range.1 hn), key_agree H (lam_lt hb) hh hj (mem_range.1 hn)]

theorem wtIJ_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) :
    AttSeg.wtIJ D t b h i j = AttSeg.wtIJ D t' b h i j := by
  have hI : i / D.B < D.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  unfold AttSeg.wtIJ
  split_ifs with hJ
  · have hs := D.slot_of_blk hJ hI
    exact wt_agree H hb
      (D.codeM_lt hh hs.1 (lt_of_lt_of_le hs.2.1 (Nat.sub_le _ _))
        (Nat.mod_lt _ D.B_pos) (Nat.mod_lt _ D.B_pos))
  · exact wt_agree H hb (D.codeD_lt hh hI (Nat.mod_lt _ D.B_pos) (Nat.mod_lt _ D.B_pos))

theorem RE_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.RE D t b h i n = AttSeg.RE D t' b h i n := by
  rw [RE_eq t b h n hi, RE_eq t' b h n hi, den_agree H hb hh hi, out_agree H hb hh hi hn]
  congr 3
  exact sum_congr rfl fun j hj => by
    rw [wtIJ_agree H hb hh hi,
      val_agree H (lam_lt hb) hh (lt_of_lt_of_le (mem_range.1 hj) (attBlk_le hi)) hn]

theorem key1_agree (hb : b < D.nb) (hx : x < 2 ^ D.lReg ρ) :
    AttSeg.key1 t ρ b x = AttSeg.key1 t' ρ b x := by
  unfold AttSeg.key1
  rw [r0_agree H hb hx, r1_agree H hb hx, fl_agree H hb hx]

theorem key2M_agree [scl : Scl] (hb : b < D.nb) (hx : x < 2 ^ D.lM) :
    AttSeg.key2 D t .M b x = AttSeg.key2 D t' .M b x := by
  have hx' : x < 2 ^ D.lReg .M := hx
  rw [key2M_eq, key2M_eq, rm_agree H hb hx', fl_agree H hb hx', wt_agree H hb hx']
  by_cases he : D.EmptyM x
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he, mx_agree H hb (D.mG_lt hx) (iM_lt he),
      attSc_agree H hb (D.mG_lt hx) (iM_lt he) (jM_lt he)]

theorem key2D_agree [scl : Scl] (hb : b < D.nb) (hx : x < 2 ^ D.lD) :
    AttSeg.key2 D t .D b x = AttSeg.key2 D t' .D b x := by
  have hx' : x < 2 ^ D.lReg .D := hx
  rw [key2D_eq, key2D_eq, rm_agree H hb hx', fl_agree H hb hx', wt_agree H hb hx',
    mx_agree H hb (D.dG_lt hx) (iD_lt x), attSc_agree H hb (D.dG_lt hx) (iD_lt x) (jD_lt x)]

theorem key3W_agree (χ : ℕ) (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.key3W D t χ b h i n = AttSeg.key3W D t' χ b h i n := by
  unfold AttSeg.key3W
  rw [RE_agree H hb hh hi hn, qh_agree H hb hh hi hn,
    qh'_agree H hb hh hi hn, den_agree H hb hh hi]

theorem key3X_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) :
    AttSeg.key3X D t b h i = AttSeg.key3X D t' b h i := by
  unfold AttSeg.key3X
  congr 2
  exact sum_congr rfl fun k hk => by rw [ib_agree H (mem_range.1 hk) hb hh hi]

theorem key4_agree (hb : b < D.nb) (hh : h < D.nG) (hi : i < D.T) (hn : n < D.ch) :
    AttSeg.key4 t b h i n = AttSeg.key4 t' b h i n := by
  unfold AttSeg.key4
  rw [qh_agree H hb hh hi hn, qh'_agree H hb hh hi hn]

/-- **The key vectors of traces that agree on the valid names are equal**, at every index. -/
theorem keyVec_agree [scl : Scl] (tb : Tables) :
    ∀ (c : Fin 4) (X : ℕ), AttSeg.keyVec D tb t c X = AttSeg.keyVec D tb t' c X
  | 0, X => by
    rw [keyVec0, keyVec0]
    exact twoFam_agree _ (fun b hb x hx => key1_agree H (ρ := .M) hb hx)
      (fun b hb x hx => key1_agree H (ρ := .D) hb hx) X
  | 1, X => by
    rw [keyVec1, keyVec1]
    exact twoFam_agree _ (fun b hb x hx => key2M_agree H hb hx)
      (fun b hb x hx => key2D_agree H hb hx) X
  | 2, X => by
    rw [keyVec2, keyVec2]
    refine twoFam_agree _
      (fun b hb y _ => key3W_agree H _ hb (Nat.mod_lt _ nG_pos)
        (Nat.mod_lt _ (AttSeg.AddrFacts.T_pos D)) (Nat.mod_lt _ ch_pos))
      (fun b hb y hy => key3X_agree H hb (Nat.div_lt_of_lt_mul ?_)
        (Nat.mod_lt _ (AttSeg.AddrFacts.T_pos D))) X
    have h2 : (2 : ℕ) ^ D.lX = D.T * D.nG := by
      show (2 : ℕ) ^ (D.lg + D.lT) = D.T * 2 ^ D.lg
      rw [D.T_eq, pow_add, Nat.mul_comm]
    rw [← h2]
    exact hy
  | 3, X => by
    rw [keyVec3, keyVec3]
    refine twoFam_agree _
      (fun b hb y hy => key4_agree H hb ?_ (Nat.mod_lt _ (AttSeg.AddrFacts.T_pos D))
        (Nat.mod_lt _ ch_pos))
      (fun _ _ _ _ => rfl) X
    show y / D.ch / D.T < D.nG
    rw [Nat.div_div_eq_div_mul]
    refine Nat.div_lt_of_lt_mul ?_
    have h2 : (2 : ℕ) ^ D.l4 = D.ch * D.T * D.nG := by
      show (2 : ℕ) ^ (D.lg + D.lT + D.ln) = 2 ^ D.ln * D.T * 2 ^ D.lg
      rw [D.T_eq, pow_add, pow_add]
      ring
    rw [← h2]
    exact hy

/-- **The identities of traces that agree on the valid names are equal.** -/
theorem idnVal_agree {j : AttSeg.Idn} (hj : j.Valid D) :
    AttSeg.idnVal D t j = AttSeg.idnVal D t' j := by
  cases j with
  | at1 k b g i =>
    obtain ⟨hk, hb, hg, hi⟩ := hj
    show AttSeg.ibV t k b g i * (AttSeg.ibV t k b g i - 1) =
      AttSeg.ibV t' k b g i * (AttSeg.ibV t' k b g i - 1)
    rw [ib_agree H hk hb hg hi]
  | at2 b g i =>
    obtain ⟨hb, hg, hi⟩ := hj
    show AttSeg.mxV t b g i - ∑ n ∈ range D.ch, AttSeg.qryV t b g i n * AttSeg.sel D t b g i n =
      AttSeg.mxV t' b g i - ∑ n ∈ range D.ch, AttSeg.qryV t' b g i n * AttSeg.sel D t' b g i n
    rw [mx_agree H hb hg hi]
    refine congrArg (AttSeg.mxV t' b g i - ·) (sum_congr rfl fun n hn => ?_)
    rw [qry_agree H hb hg hi (mem_range.1 hn)]
    refine congrArg (AttSeg.qryV t' b g i n * ·) ?_
    unfold AttSeg.sel
    refine sum_congr rfl fun j hj => ?_
    rw [key_agree H (lam_lt hb) hg (mem_range.1 hj) (mem_range.1 hn)]
    refine congrArg (AttSeg.keyV t' (D.lamOf b) g j n * ·) ?_
    exact prod_congr rfl fun k hk => by rw [ib_agree H (mem_range.1 hk) hb hg hi]
  | at3 b g i =>
    obtain ⟨hb, hg, hi⟩ := hj
    show AttSeg.denV t b g i - AttSeg.rowSum D t (fun _ => 1) b g i =
      AttSeg.denV t' b g i - AttSeg.rowSum D t' (fun _ => 1) b g i
    rw [den_agree H hb hg hi, AttSeg.rowSum_eq D t _ b g hi, AttSeg.rowSum_eq D t' _ b g hi]
    exact congrArg (AttSeg.denV t' b g i - ·)
      (sum_congr rfl fun j _ => by rw [wtIJ_agree H hb hg hi])

end Agree

/-- **The relation reads valid names only.** -/
theorem rfraw_valid [scl : Scl] {tb : Tables} {F : Type} [CommRing F] {t t' : Raw → ℤ}
    (H : ∀ c : Raw, c.Valid D → t c = t' c) (h : AttSeg.RFraw D tb F t) :
    AttSeg.RFraw D tb F t' := by
  have HF : AgreeD D (AttSeg.castT t : Raw → F) (AttSeg.castT t') := fun c hc => by
    show ((t c : ℤ) : F) = ((t' c : ℤ) : F)
    rw [H c hc]
  refine ⟨fun c hc => ?_, fun c X hX => ?_, fun j hj => ?_⟩
  · rw [← H c hc]
    exact h.1 c hc
  · rw [← keyVec_agree HF tb c X]
    exact h.2.1 c X hX
  · rw [← idnVal_agree HF hj]
    exact h.2.2 j hj

end OnBytes.Road.L5.V

#print axioms OnBytes.Road.L5.V.keyVec_agree
#print axioms OnBytes.Road.L5.V.idnVal_agree
#print axioms OnBytes.Road.L5.V.rfraw_valid
