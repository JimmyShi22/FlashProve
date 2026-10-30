-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortLate.lean: the forms that the verifier's claims 6, 7 and 8 of an attention
sub-proof read are the library-side reading forms of the last four sumchecks, at any values of the
late entries.

Cb/Pv/Att/End/Last.lean writes, in the library's names, the forms that the claims on the end values
of the last four sumchecks read: rA12, rB12, rM6, rA16, rKC, rIBP, rA21. This file holds them
against the forms that the verifier makes (OnBytes/Model/AttentionClaimsB.lean). No table is taken
to be true: the entries of the vector of tables are as they were sent. What ties the two sides is
the dictionary LateAt (Johnson/Road/Rows/AttEntRow.lean), with the places of this file.

Main definitions.
 - placeLong S r: the place, within a table on blocks of features, of the entry whose first cell has
   the name r.
 - placeAtt S T: the places of the table named T.
 - LateTabs h tabOf: where the seven tables of these claims begin.
Main theorems. Each says: the form that the verifier's function returns is worth what the
library-side form is worth at Sum.elim m u, for all m and u that meet the dictionary.
 - max_port (rM6), query_port (rA16), key_port (rKC), ibit_port (rIBP), value_port (the read in
   rB12), weight_port (the two reads in rA12), bits_port (the loop of claim 8 against rA21 with 4
   variables for the number of a bit, the verifier's number; the library's own number is 4 only for
   requests of 2^9 to 2^16 tokens).
 - end_port: so a claim "the slot's hidden value less the form is 0" has the value 0 if and only if
   the library-side claim endF holds, if the slot's hidden value is what endF says it is.

What the theorems take as given: the setting (AttPub: numerals, the shape's return); the number of
columns of the vector in the state in which a form is made (Cols); the dictionary; where the seven
tables begin (LateTabs); that the names read are names of late entries; the lengths of the
verifier's points; the number of limbs of a tensor and of bits of a region's entries; that the
library's points and challenges (ξ, and those that a statement names) are the verifier's, coordinate
by coordinate; that the routine has returned.

What is not claimed. That the dictionary holds of the programs' message. The theorems of this file
use the places of seven tables (tVD, qVD, hT, qF, qKx, hPi, hR2): there a place is shown to be the
number at which the verifier's function reads. The other fourteen:
Johnson/Road/Rows/AttPortFirst.lean (eight) and Johnson/Road/Rows/AttPortLin.lean (six). That the
verifier adds just these claims. Nothing is said about probabilities or about hiding. The program
does not import this file.


-/
import Johnson.Road.Rows.AttEntLong
import Johnson.Road.Rows.AttEnds58Proofs
import Cb.Pv.Att.End.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff Fork SubM eqTab ofNat)
open OnBytes.Attention (Heard sc3A minusOne)
open OnBytes.Road.Hd (Ok ok_pure ok_bind rdW)
open Inst.Model.AttSeg (Raw Calls Pub sh yn)
open Cb.Pv.Att (eqN_agree)
open Cb.Pv.Att.End (LateLay AttTab rdRow rdLong rdCol rdRow_congr rdLong_congr rdCol_congr rM6
  rA16 rKC rIBP rA21 rA12 rB12 ptOn val_aSum val_aSmul val_aAdd val_aConst)

variable {K : Type} [Field K]

/-! ## Places -/

/-- The place, within a table on blocks of features, of the entry whose first cell has the name r.
-/
def placeLong (S : Attention.Shape) : Raw → ℕ
  | .qry k b g _ n => placeTen S S.atQ k (b / S.HA) (g * S.HA + b % S.HA) n
  | .out k b g _ n => placeTen S S.atO k (b / S.HA) (g * S.HA + b % S.HA) n
  | .key k lam g _ n => placeTen S S.atK k lam g n
  | .val k lam g _ n => placeTen S S.atV k lam g n
  | .qh b g _ n => placeTen S (Attention.atRh S) 0 (b / S.HA) (g * S.HA + b % S.HA) n
  | .qh' b g _ n => placeTen S (Attention.atRhp S) 0 (b / S.HA) (g * S.HA + b % S.HA) n
  | _ => 0

/-- The places of the table named T. -/
def placeAtt (S : Attention.Shape) : AttTab → Raw → ℕ
  | .tA => placeCol S
  | .tVM => placeCol S
  | .tVD => placeCol S
  | .tMm => placeRow S
  | .tMd => placeRow S
  | .hW => placeRow S
  | .hX => placeRow S
  | .hE => placeRow S
  | .hT => placeRow S
  | .hPi => placeRow S
  | .hR2 => placeRow S
  | _ => placeLong S

/-- Where the seven tables of the claims 6, 7 and 8 on end values begin. -/
structure LateTabs (h : Heard) (tabOf : AttTab → ℕ) : Prop where
  tVD : tabOf .tVD = h.t.tVD
  qVD : tabOf .qVD = h.t.qVD
  hT : tabOf .hT = h.t.hT
  qF : tabOf .qF = h.t.qF
  qKx : tabOf .qKx = h.t.qKx
  hPi : tabOf .hPi = h.t.hPi
  hR2 : tabOf .hR2 = h.t.hR2

section
variable {ρ : Reading K} {W : World K} {K3 : ℕ} {h : Heard} {lid : ℕ} {cf : Attention.Cfg}
  {fs : Model.Forest.Shape} {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁]
  [DecidableEq J₂] {Y : LateLay AttTab J₂} {tabOf : AttTab → ℕ} {u : J₂ → K} (m : J₁ → K)
  {F : Fork} {C : Ctx} {q : Aff} {G : Fork} {D : Ctx}

/-- The library's number of bits of a position is the shape's. -/
theorem pub_lT (A : AttPub ρ h lid cf fs) : (L5.dimOf h.S).lT = h.S.cf.lt := by
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have N := L5.norm_of_shaped (L5.shaped_of_hid A.shape) (L5.tested_of_shape hS0).1
    (L5.tested_of_shape hS0).2
  exact N.lt.symm

/-! ## Tables on single features -/

/-- The row maximum of claim 7. -/
theorem max_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {p : Pub K} {b : ℕ}
    (hb : b < h.S.NP) (htg : h.x.tg.size = h.S.cf.lgk)
    (hp : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, Y.good (.hT, .mx l b g 0))
    (hh : Ok (Attention.readMaximum h h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA)) F C q G D) :
    q.value ρ W = (rM6 (J₁ := J₁) (L5.dimOf h.S) Y p b).val (Sum.elim m u) := by
  have e0 : b / h.S.HA * h.S.HA + b % h.S.HA = b := Nat.div_add_mod' b h.S.HA
  rw [← Tb.hT] at hh
  rw [readMaximum_row m A hc L .hT rfl (Nat.le_of_eq htg.symm) (Nat.mod_lt b (heads_pos hb))
    (by rw [e0]; exact hg) hh, e0]
  exact rdRow_congr _ _ _ _ hp _ _

/-- A bit of the index, of claim 7. ξ: the point of the key at the index. -/
theorem ibit_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {ξ : ℕ → K} {b k : ℕ}
    (hb : b < h.S.NP) (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ξ j = pt ρ h.x.scd.r j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, Y.good (.hPi, .ib k b g 0))
    (hh : Ok (Attention.readIndexBit h h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k)
      F C q G D) :
    q.value ρ W = (rIBP (J₁ := J₁) (L5.dimOf h.S) Y ξ b k).val (Sum.elim m u) := by
  have e0 : b / h.S.HA * h.S.HA + b % h.S.HA = b := Nat.div_add_mod' b h.S.HA
  have hlT := pub_lT A
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  rw [← Tb.hPi] at hh
  rw [readIndexBit_row m A hc L .hPi rfl (Nat.le_of_eq s1.symm) (Nat.mod_lt b (heads_pos hb))
    (by rw [e0]; exact hg) hh, e0]
  refine rdRow_congr _ _ _ _ (fun j hj => ?_) _ _
  have hj' : j < h.S.cf.lgk := hj
  show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j = ξ ((L5.dimOf h.S).lT + j)
  rw [hlT, hξ _ (by omega)]
  exact pt_extract ρ _ (by omega) (by omega)

/-- The loop of claim 8. The form that it makes is worth the hidden value under the first end
value's slot, less what rA21 with 4 variables for the number of a bit is worth. ξ: the point of the
sumcheck for the bits. -/
theorem bits_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {ξ : ℕ → K} {b : ℕ}
    (hb : b < h.S.NP) (hr : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ξ j = pt ρ h.x.scH.r j)
    (hg : ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, Y.good (.hR2, .ib k b g 0))
    (hh : Ok (bitsForm h b) F C q G D) :
    q.value ρ W = W.slot (h.x.scH.sEnd + 2 * b) -
      (rA21 (J₁ := J₁) (L5.dimOf h.S) Y 4 ξ b).val (Sum.elim m u) := by
  have e0 : b / h.S.HA * h.S.HA + b % h.S.HA = b := Nat.div_add_mod' b h.S.HA
  have hlT := pub_lT A
  obtain ⟨S0, hS0⟩ := L5.shape_of_hid A.shape
  have h16 : h.S.cf.lt ≤ 16 := by
    rw [(L5.shaped_of_hid A.shape).cfg]
    exact lt_le_16 hS0
  have s1 : (h.x.rg2 h.S).size = h.S.cf.lgk := by
    show (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s3 : (h.x.rk h.S).size = 4 := by
    show (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4)).size = _
    rw [size_cut _ (by omega)]
    omega
  have ha := Nat.mod_lt b (heads_pos hb)
  obtain ⟨-, -, -, e⟩ := foldlM_value ρ W F C
    (fun s k => Attention.readIndexBit h h.t.hR2 (h.x.rg2 h.S) (b / h.S.HA) (b % h.S.HA) k >>=
      fun bit => pure (Aff.addMul s bit (mulE minusOne ((eqTab (h.x.rk h.S)).getD k zeroE))))
    (fun k => -(Blocks.eqN 4 0 (sh ξ ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg)) k *
      (rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hR2 (sh ξ (L5.dimOf h.S).lT) 1
        fun _ g => .ib k b g 0).val (Sum.elim m u)))
    (fun _ => True) (List.range h.S.cf.lt)
    (by
      intro k hk s y G1 D1 hy
      have hk' : k < h.S.cf.lt := List.mem_range.mp hk
      rw [ok_bind] at hy
      obtain ⟨bit, F1, C1, h1, h2⟩ := hy
      obtain ⟨a1, a2, -⟩ := limbs_ent W A hc (Nat.le_of_eq s1.symm)
        (fun g => k * h.S.cf.H + g * h.S.HA + b % h.S.HA) h1
      rw [← Tb.hR2] at h1
      have a3 := readIndexBit_row m A hc L .hR2 rfl (Nat.le_of_eq s1.symm) ha
        (by rw [e0]; exact hg k hk') h1
      rw [ok_pure] at h2
      obtain ⟨b1, b2, b3⟩ := h2
      rw [b1, b2, b3]
      refine ⟨a1, a2, trivial, ?_⟩
      rw [e0] at a3
      have w1 : ρ.val ((eqTab (h.x.rk h.S)).getD k zeroE) =
          Blocks.eqN 4 0 (sh ξ ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg)) k := by
        rw [eqTab_value ρ _ k (by rw [s3]; omega), s3]
        refine eqN_agree (fun j hj => ?_) k
        show pt ρ (h.x.scH.r.extract (h.S.cf.lt + h.S.cf.lgk) (h.S.cf.lt + h.S.cf.lgk + 4))
          (0 + j) = ξ ((L5.dimOf h.S).lT + h.S.cf.lgk + (0 + j))
        rw [hlT, Nat.zero_add, hξ _ (by omega)]
        exact pt_extract ρ _ (by omega) (by omega)
      have w2 : (rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hR2 (pt ρ (h.x.rg2 h.S)) 1
          fun _ g => .ib k b g 0).val (Sum.elim m u) =
          (rdRow (J₁ := J₁) (L5.dimOf h.S) Y .hR2 (sh ξ (L5.dimOf h.S).lT) 1
            fun _ g => .ib k b g 0).val (Sum.elim m u) := by
        refine rdRow_congr _ _ _ _ (fun j hj => ?_) _ _
        have hj' : j < h.S.cf.lgk := hj
        show pt ρ (h.x.scH.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j =
          ξ ((L5.dimOf h.S).lT + j)
        rw [hlT, hξ _ (by omega)]
        exact pt_extract ρ _ (by omega) (by omega)
      have w3 : ρ.val minusOne = -1 := by
        show ρ.val (subE zeroE oneE) = -1
        rw [ρ.sub, ρ.zero, ρ.one, zero_sub]
      rw [Aff.value_addMul, ρ.mul, w3, w1, a3, w2]
      ring)
    (sc3A h.x.scH b) q G D hh
  have e1 : (sc3A h.x.scH b).value ρ W = W.slot (h.x.scH.sEnd + 2 * b) := Aff.value_slot ρ W _
  rw [e, e1, sum_map_range, ← hlT, sum_neg_distrib]
  unfold Cb.Pv.Att.End.rA21
  rw [val_aSum, sub_eq_add_neg]
  congr 2
  exact sum_congr rfl fun k _ => by rw [val_aSmul]

/-! ## Tables on blocks of features -/

/-- The query of claim 7. ξ: the point of the score at the index. -/
theorem query_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {ξ : ℕ → K} {b : ℕ}
    (hnl : h.S.atQ.nl = 2)
    (hr : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ξ j = pt ρ h.x.scF.r j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qF, (Raw.qry l b g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readHead h h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA)
      (b % h.S.HA)) F C q G D) :
    q.value ρ W = (rA16 (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y ξ b).val (Sum.elim m u) := by
  have hlT := pub_lT A
  have s1 : (h.x.rg h.S).size = h.S.cf.lgk := by
    show (h.x.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.rc h.S).size = h.S.cf.ldh := by
    show (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  rw [← Tb.qF] at hh
  rw [head_long m A hc L .qF (fun g => g * h.S.HA + b % h.S.HA) (Nat.le_of_eq s1.symm) s2
    (fun l g => .qry l b g 0 0) (by rw [hnl]; exact hg)
    (fun g ch l _ => by
      show placeTen h.S h.S.atQ l (b / h.S.HA) (g * h.S.HA + b % h.S.HA) (0 + ch * 2 ^ h.S.ls) = _
      unfold placeTen
      rw [blk_div]) hh, hnl]
  refine rdLong_congr _ _ _ _ _ (fun j hj => ?_) (fun j hj => ?_) _ _
  · have hj' : j < h.S.cf.lgk := hj
    show pt ρ (h.x.scF.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j = ξ ((L5.dimOf h.S).lT + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (by omega) (by omega)
  · have hj' : j < h.S.cf.ldh - h.S.ls := hj
    show pt ρ (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size) j =
      ξ ((L5.dimOf h.S).lT + h.S.cf.lgk + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (Nat.le_refl _) (by omega)

/-- The key of claim 7. ξ: the point of the key at the index. -/
theorem key_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {p : Pub K} {ξ : ℕ → K}
    {lam : ℕ} (hnl : h.S.atK.nl = 2)
    (hrF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh)
    (hr : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk)
    (hξ : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ξ j = pt ρ h.x.scd.r j)
    (hfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = p.fn j)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qKx, (Raw.key l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readGroup h h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam) F C q G D) :
    q.value ρ W = (rKC (J₁ := J₁) (L5.dimOf h.S) h.S.ls Y p ξ lam).val (Sum.elim m u) := by
  have hlT := pub_lT A
  have s1 : (h.x.pg h.S).size = h.S.cf.lgk := by
    show (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)).size = _
    rw [size_cut _ (by omega)]
    omega
  have s2 : (h.x.rc h.S).size = h.S.cf.ldh := by
    show (h.x.scF.r.extract (h.S.cf.lt + h.S.cf.lgk) h.x.scF.r.size).size = _
    rw [size_cut _ (Nat.le_refl _)]
    omega
  rw [← Tb.qKx] at hh
  rw [head_long m A hc L .qKx (fun g => g) (Nat.le_of_eq s1.symm) s2
    (fun l g => .key l lam g 0 0) (by rw [hnl]; exact hg)
    (fun g ch l _ => by
      show placeTen h.S h.S.atK l lam g (0 + ch * 2 ^ h.S.ls) = _
      unfold placeTen
      rw [blk_div]) hh, hnl]
  refine rdLong_congr _ _ _ _ _ (fun j hj => ?_) (fun j hj => ?_) _ _
  · have hj' : j < h.S.cf.lgk := hj
    show pt ρ (h.x.scd.r.extract h.S.cf.lt (h.S.cf.lt + h.S.cf.lgk)) j = ξ ((L5.dimOf h.S).lT + j)
    rw [hlT, hξ _ (by omega)]
    exact pt_extract ρ _ (by omega) (by omega)
  · have hj' : j < h.S.cf.ldh - h.S.ls := hj
    exact hfn j (by omega)

/-- The value of claim 6, on the diagonal tiles. ξ: the point of the value product there. -/
theorem value_port (A : AttPub ρ h lid cf fs) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {Cc : Calls} {p : Pub K}
    {ξ : ℕ → K} {b lam : ℕ} (hlam : (L5.dimOf h.S).lamOf b = lam) (hnl : h.S.atV.nl = 2)
    (hr : h.S.cf.lgk ≤ h.d.vpd.r.size) (hzc : h.d.zcW.size = h.S.cf.ldh)
    (hξ : ∀ j < h.S.cf.lgk, ξ j = pt ρ h.d.vpd.r j)
    (hyn : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn (L5.dimOf h.S) Cc p.z j)
    (hgam : ρ.val h.d.gam = p.th)
    (hg : ∀ g < 2 ^ h.S.cf.lgk, ∀ ch < 2 ^ (h.S.cf.ldh - h.S.ls), ∀ l < 2,
      Y.good (.qVD, (Raw.val l lam g 0 0).addN (ch * 2 ^ h.S.ls)))
    (hh : Ok (Attention.readGroup h h.t.qVD h.S.atV h.d.vpd.r h.d.zcW lam) F C q G D) :
    (Aff.ofConst h.d.gam + q).value ρ W =
      (rB12 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.ls Y p ξ b).val (Sum.elim m u) := by
  rw [← Tb.qVD] at hh
  unfold Cb.Pv.Att.End.rB12
  rw [Aff.value_add, Aff.value_ofConst, hgam, val_aAdd, val_aConst, hlam,
    head_long m A hc L .qVD (fun g => g) hr hzc
    (fun l g => .val l lam g 0 0) (by rw [hnl]; exact hg)
    (fun g ch l _ => by
      show placeTen h.S h.S.atV l lam g (0 + ch * 2 ^ h.S.ls) = _
      unfold placeTen
      rw [blk_div]) hh, hnl]
  congr 1
  refine rdLong_congr _ _ _ _ _ (fun j hj => (hξ j hj).symm) (fun j hj => ?_) _ _
  have hj' : j < h.S.cf.ldh - h.S.ls := hj
  exact hyn j (by omega)

/-! ## The table on the regions' entries -/

/-- The softmax weight of claim 6, on the diagonal tiles. ξ: the point of the value product there.
p3, p4: the forms of the two planes. -/
theorem weight_port (hN : Numerals ρ) (hc : Cols F h K3)
    (L : LateAt W h K3 Y tabOf (placeAtt h.S) u) (Tb : LateTabs h tabOf) {Cc : Calls} {p : Pub K}
    {ξ : ℕ → K} {lam a : ℕ} (ha : a < h.S.HA) (hnD : (L5.dimOf h.S).lD = h.S.nD)
    (hz : h.t.ptD.size = h.S.nD)
    (hpt : ∀ j < h.S.nD - h.S.cf.lmS, pt ρ h.t.ptD j = ptOn (L5.dimOf h.S) Cc p ξ j)
    (hg : ∀ jj < 5, ∀ hi < 2 ^ (h.S.nD - h.S.cf.lmS),
      Y.good (.tVD, (Raw.c .D jj (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS)))
    {p3 p4 : Aff} {F' G' : Fork} {C' D' : Ctx} (hc' : Cols F' h K3)
    (h3 : Ok (Attention.plane h h.t.tVD 3 lam a h.t.ptD true) F C p3 G D)
    (h4 : Ok (Attention.plane h h.t.tVD 4 lam a h.t.ptD true) F' C' p4 G' D') :
    (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256)).value ρ W =
      (rA12 (J₁ := J₁) (L5.dimOf h.S) Cc h.S.cf.lmS Y p ξ (lam * h.S.HA + a)).val
        (Sum.elim m u) := by
  have hb := pair_parts (lam := lam) ha
  rw [← Tb.tVD] at h3 h4
  have pl : ∀ x hi, placeAtt h.S .tVD
      ((Raw.c .D x (lam * h.S.HA + a) 0).addX (hi * 2 ^ h.S.cf.lmS)) =
      planeFirst h.S x lam a true >>> h.S.cf.lmS + hi := by
    intro x hi
    show planeFirst h.S x ((lam * h.S.HA + a) / h.S.HA) ((lam * h.S.HA + a) % h.S.HA) true >>>
      h.S.cf.lmS + (0 + hi * 2 ^ h.S.cf.lmS) / 2 ^ h.S.cf.lmS = _
    rw [hb.1, hb.2, blk_div]
  have e3 := plane_col (ρ := ρ) m hc L .tVD (nb := h.S.nD) (if_pos rfl) hz
    (.c .D 3 (lam * h.S.HA + a) 0) (hg 3 (by norm_num)) (pl 3) h3
  have e4 := plane_col (ρ := ρ) m hc' L .tVD (nb := h.S.nD) (if_pos rfl) hz
    (.c .D 4 (lam * h.S.HA + a) 0) (hg 4 (by norm_num)) (pl 4) h4
  unfold Cb.Pv.Att.End.rA12
  rw [Aff.value_add, Aff.value_add, Aff.value_ofConst, Aff.value_scale, hN.ofNat, hN.ofNat, e3, e4,
    val_aAdd, val_aAdd, val_aConst, val_aSmul, hnD,
    rdCol_congr _ _ _ _ _ hpt, rdCol_congr _ _ _ _ _ hpt]
  push_cast
  ring

end

/-! ## From forms to claims -/

/-- A claim of the verifier on an end value is the library-side claim. j: the end value's slot; q:
the form that the verifier reads; r: the library-side form. hs: the hidden value under the slot is
what was shown less the last coordinate times the mask entry. -/
theorem end_port [Fintype K] {ρ : Reading K} {W : World K} (T : Cb.Pv.Att.PlainSc K) {J₂ : Type}
    [Fintype J₂] [DecidableEq J₂] [DecidableEq T.J] (o : T.our.par.Out) (a : T.A)
    (r : TWhole.Aff K (T.J ⊕ J₂)) (x : T.J ⊕ J₂ → K) (j : ℕ) (q : Aff)
    (hs : W.slot j = o.vals a - T.our.lst o.st (T.our.par.hp o.st o.pt) * x (.inl (T.cAt a)))
    (hq : q.value ρ W = r.val x) :
    (Aff.slot j - q).value ρ W = 0 ↔ (Cb.Pv.Att.End.endF T o a r).Holds x := by
  rw [Cb.Pv.Att.End.endF_at, Aff.value_sub, Aff.value_slot, hs, hq]
  exact sub_eq_zero

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.max_port
#print axioms OnBytes.Road.Rows.ibit_port
#print axioms OnBytes.Road.Rows.bits_port
#print axioms OnBytes.Road.Rows.query_port
#print axioms OnBytes.Road.Rows.key_port
#print axioms OnBytes.Road.Rows.value_port
#print axioms OnBytes.Road.Rows.weight_port
#print axioms OnBytes.Road.Rows.end_port
