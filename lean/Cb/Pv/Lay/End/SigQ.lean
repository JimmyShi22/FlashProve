-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/SigQ.lean: the share of the panel QK is the summand of the family QK at
the end point of the sumcheck over the positions: the library with itself.

The keys of the family QK hold the rotated products of the array a with the matrices of queries and
keys. Inst/Model/FF/Objects.lean has them twice at a point zh of the positions: in termHat .QK,
entry by entry, each entry rotated with its partner in the pair under the entry's weight ew; and in
the panel QK, whose B side has the weights of the heads (AH), the rotated weights within a head
(kp) and the matrix by heads (Wqk). This file shows that the two agree.

Every statement here compares objects of the library with objects of the library. The file imports
no file of OnBytes/.

Main theorems: share_QK, hat_QK; ew_QK_split (the weight of entry x of head h is AH h times lf x),
AYU_split, head_swap, pair_swap (the rotation of pairs moved from one factor to the other),
scl_kQK, shifts_of_lawful.

The hypotheses, and that they can be met.
 - Dim.ChOK: the width of a head is a power of two, at least 2, and fits the call's columns. Met by
   the reference sizes (ref_chOK in Inst/Model/FF/Objects.lean).
 - For each layer of the segment the shifts kq and kk are equal or both at least 16. The panel's
   weight has the factor of kq for all heads, the summand that of kq on the query heads and of kk
   on the key heads; under this clause the two factors are one. It is the field qk of the library's
   LawfulW (Inst/Model/FF/ScalesDef.lean): every lawful table meets it (shifts_of_lawful), and the
   library's reference table is lawful. At the small public example LawfulW fails in every layer
   (by a run that is no part of this folder); whether this one clause holds there is run nowhere.

What is not claimed. Nothing is said of the other panels (see Cb/Pv/Lay/End/SigG.lean), of
the sumcheck over the positions, or of what a verifier's acceptance shows. The program does
not import this file.


-/
import Inst.Model.FF.Objects
import Inst.Model.FF.IndexFacts
import Inst.Model.FF.Lawful

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Sig

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan rdTrue termHat ew ewc el wc valU AH lf kp Wqk AYU Ct St
  kQK lch lJ call pos len zc)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A sum over an even number of terms, by pairs. -/
theorem sum_pairs (m : ℕ) (g : ℕ → K) :
    ∑ x ∈ range (m * 2), g x = ∑ j ∈ range m, (g (2 * j) + g (2 * j + 1)) := by
  rw [Alg.sum_range_mul_add]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_range_succ, sum_range_one, Nat.mul_comm j 2, Nat.add_zero]

/-- The rotation of pairs, moved from one factor to the other. On the left each entry x of a vector
Y is rotated with its partner under the weight u x; on the right the weights are rotated the other
way. c j, s j: the cosine and the sine of pair j. -/
theorem pair_swap (m : ℕ) (u c s Y : ℕ → K) :
    ∑ x ∈ range (m * 2), u x * (if x % 2 = 0 then c (x / 2) * Y x - s (x / 2) * Y (x + 1)
        else s (x / 2) * Y (x - 1) + c (x / 2) * Y x) =
      ∑ x ∈ range (m * 2), (if x % 2 = 0 then c (x / 2) * u x + s (x / 2) * u (x + 1)
        else c (x / 2) * u x - s (x / 2) * u (x - 1)) * Y x := by
  rw [sum_pairs, sum_pairs]
  refine sum_congr rfl fun j _ => ?_
  have a1 : (2 * j) % 2 = 0 := by omega
  have a2 : (2 * j) / 2 = j := by omega
  have a3 : ¬ (2 * j + 1) % 2 = 0 := by omega
  have a4 : (2 * j + 1) / 2 = j := by omega
  have a5 : 2 * j + 1 - 1 = 2 * j := by omega
  rw [if_pos a1, if_neg a3, if_pos a1, if_neg a3, a2, a4, a5]
  ring

/-- The factor of a shift goes through a sum. -/
theorem scl_sum (k n : ℕ) (f : ℕ → K) :
    ∑ x ∈ range n, Inst.Model.Site.scl k (f x) = Inst.Model.Site.scl k (∑ x ∈ range n, f x) := by
  simp only [Inst.Model.Site.scl_eq, mul_sum]

/-! ## The weights of the family QK, head by head -/

section Heads

variable (D : Dim)

/-- The family QK has one stretch of ch entries for each head. -/
theorem dqk_heads : D.dqk = (D.P.nq + D.P.nkv) * D.P.ch := by
  show D.P.nq * D.P.ch + D.P.nkv * D.P.ch = _
  ring

/-- The weight of entry x of head h of the family QK is the head's weight times the weight of x
within a head. -/
theorem ew_QK_split (C : D.ChOK) (z : ℕ → K) {h x : ℕ} (hh : h < D.P.nq + D.P.nkv)
    (hx : x < D.P.ch) : ew D z .QK (h * D.P.ch + x) = AH D z h * lf D z x := by
  have hp := C.pow
  have hx' : x < 2 ^ lch D := hp ▸ hx
  have hpos : 0 < 2 ^ lch D := Nat.two_pow_pos _
  have hlen : len D .QK = 2 ^ lch D * (D.P.nq + D.P.nkv) := by
    show D.dqk = _
    rw [dqk_heads, hp, Nat.mul_comm]
  obtain ⟨a1, q, hq⟩ := Inst.Model.FFSeg.IndexFacts.posAligned D .QK (lch D) h x ⟨_, hlen⟩
    (by rw [hlen]; exact (Nat.mul_lt_mul_left hpos).mpr hh) hx'
  have e1 : h * D.P.ch + x = 2 ^ lch D * h + x := by rw [hp, Nat.mul_comm]
  have e2 : D.P.ch * h = 2 ^ lch D * h := by rw [hp]
  have e3 : lJ D (call .QK) = (lJ D (call .QK) - lch D) + lch D :=
    (Nat.sub_add_cancel C.col).symm
  have eA : AH D z h = Blocks.eqN (lJ D (call .QK) - lch D) D.lL (zc D z (call .QK)) q := by
    unfold AH
    rw [e2, hq, hp, Nat.mul_div_cancel_left q hpos]
  have eE : ew D z .QK (h * D.P.ch + x) =
      Blocks.eqN ((lJ D (call .QK) - lch D) + lch D) D.lL (zc D z (call .QK))
        (2 ^ lch D * q + x) := by
    rw [← e3, e1]
    unfold ew ewc
    rw [a1, hq]
  rw [eE, eA, Blocks.eqN_append _ _ _ _ q hx']
  rfl

variable (t : Cell → K) (w : ℕ → LW K)

/-- The extension of AY at entry x of head h: the extensions of a with the column (h, x) of the
matrix of queries and keys. -/
theorem AYU_split (l : ℕ) (X : ℕ → K) (h : ℕ) {x : ℕ} (hx : x < D.P.ch) :
    AYU D t w l (h * D.P.ch + x) X =
      ∑ j ∈ range D.d, valU D t .a l j X * Wqk D w l j h x := by
  unfold AYU Wqk
  by_cases hq : h < D.P.nq
  · have h1 : (h + 1) * D.P.ch ≤ D.P.nq * D.P.ch := Nat.mul_le_mul_right _ hq
    have h2 : (h + 1) * D.P.ch = h * D.P.ch + D.P.ch := Nat.succ_mul _ _
    have h3 : h * D.P.ch + x < D.dq := by
      show _ < D.P.nq * D.P.ch
      omega
    rw [if_pos h3]
    refine sum_congr rfl fun j _ => ?_
    rw [if_pos hq, Nat.mul_comm]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.not_lt.mp hq)
    have h3 : ¬ (D.P.nq + k) * D.P.ch + x < D.dq := by
      show ¬ _ < D.P.nq * D.P.ch
      rw [Nat.add_mul]
      omega
    have h4 : (D.P.nq + k) * D.P.ch + x - D.dq = D.P.ch * k + x := by
      show _ - D.P.nq * D.P.ch = _
      rw [Nat.add_mul, Nat.add_assoc, Nat.add_sub_cancel_left, Nat.mul_comm]
    rw [if_neg h3]
    refine sum_congr rfl fun j _ => ?_
    rw [if_neg hq, h4, Nat.add_sub_cancel_left]

end Heads

/-! ## The summand of the family QK -/

section Hat

variable [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
  (z zh : ℕ → K)

/-- The factor of the shift of QK at an entry is that of the queries' shift, if the two shifts are
equal or both at least 16. -/
theorem scl_kQK {l : ℕ}
    (hk : (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk)) (x : ℕ) (v : K) :
    Inst.Model.Site.scl (kQK D l x) v = Inst.Model.Site.scl (D.Pl l).kq v := by
  unfold kQK
  split_ifs
  · rfl
  · rcases hk with e | ⟨h1, h2⟩
    · rw [e]
    · rw [Inst.Model.Site.scl_of_le h1, Inst.Model.Site.scl_of_le h2]

/-- A lawful table of scales has the clause on the shifts of queries and keys in every layer. The
library's reference table is lawful (the instance in Inst/Model/FF/Lawful.lean). -/
theorem shifts_of_lawful [Inst.Model.FFSeg.Lawful] (l : ℕ) :
    (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk) :=
  (Inst.Model.FFSeg.Lawful.all l).qk

omit scl in
/-- One head's part of the summand: the rotation is moved from the extensions of AY to the weights
within a head. -/
theorem head_swap (C : D.ChOK) (l h : ℕ) :
    ∑ x ∈ range D.P.ch, lf D z x *
        (if x % 2 = 0 then
          Ct D tb L0 l (x / 2) zh * AYU D t w l (h * D.P.ch + x) zh -
            St D tb L0 l (x / 2) zh * AYU D t w l (h * D.P.ch + (x + 1)) zh
        else
          St D tb L0 l (x / 2) zh * AYU D t w l (h * D.P.ch + (x - 1)) zh +
            Ct D tb L0 l (x / 2) zh * AYU D t w l (h * D.P.ch + x) zh) =
      ∑ x ∈ range D.P.ch, kp D tb L0 z zh l x * AYU D t w l (h * D.P.ch + x) zh := by
  have hm : D.P.ch = 2 ^ (lch D - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel C.two]
    exact C.pow
  have e := pair_swap (2 ^ (lch D - 1)) (lf D z) (fun j => Ct D tb L0 l j zh)
    (fun j => St D tb L0 l j zh) (fun x => AYU D t w l (h * D.P.ch + x) zh)
  rw [← hm] at e
  exact e

/-- The summand of the family QK at the end point, in the words of the panel QK. Asked: what the
panel needs of the sizes (Dim.ChOK), and that the shifts of queries and keys of the layer are equal
or both at least 16. -/
theorem hat_QK (C : D.ChOK) {l : ℕ}
    (hk : (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk)) :
    termHat D t tb L0 w z .QK l zh =
      Inst.Model.Site.scl (D.Pl l).kq (∑ j ∈ range D.d, valU D t .a l j zh *
        ∑ h ∈ range (D.P.nq + D.P.nkv), ∑ x ∈ range D.P.ch,
          AH D z h * kp D tb L0 z zh l x * Wqk D w l j h x) := by
  have hc0 : 0 < D.P.ch := by
    rw [C.pow]
    exact Nat.two_pow_pos _
  show ∑ x ∈ range D.dqk, ew D z .QK x * Inst.Model.Site.scl (kQK D l x)
    (if (x % D.P.ch) % 2 = 0 then
      Ct D tb L0 l (x % D.P.ch / 2) zh * AYU D t w l x zh -
        St D tb L0 l (x % D.P.ch / 2) zh * AYU D t w l (x + 1) zh
    else
      St D tb L0 l (x % D.P.ch / 2) zh * AYU D t w l (x - 1) zh +
        Ct D tb L0 l (x % D.P.ch / 2) zh * AYU D t w l x zh) = _
  simp only [scl_kQK D hk, Inst.Model.Site.mul_scl]
  rw [scl_sum, dqk_heads, Alg.sum_range_mul_add]
  congr 1
  -- head by head
  have e1 : ∀ h, h < D.P.nq + D.P.nkv → ∑ x ∈ range D.P.ch, ew D z .QK (h * D.P.ch + x) *
      (if ((h * D.P.ch + x) % D.P.ch) % 2 = 0 then
        Ct D tb L0 l ((h * D.P.ch + x) % D.P.ch / 2) zh * AYU D t w l (h * D.P.ch + x) zh -
          St D tb L0 l ((h * D.P.ch + x) % D.P.ch / 2) zh *
            AYU D t w l (h * D.P.ch + x + 1) zh
      else
        St D tb L0 l ((h * D.P.ch + x) % D.P.ch / 2) zh * AYU D t w l (h * D.P.ch + x - 1) zh +
          Ct D tb L0 l ((h * D.P.ch + x) % D.P.ch / 2) zh *
            AYU D t w l (h * D.P.ch + x) zh) =
      AH D z h * ∑ x ∈ range D.P.ch, kp D tb L0 z zh l x *
        ∑ j ∈ range D.d, valU D t .a l j zh * Wqk D w l j h x := by
    intro h hh
    have e2 : ∑ x ∈ range D.P.ch, kp D tb L0 z zh l x *
        ∑ j ∈ range D.d, valU D t .a l j zh * Wqk D w l j h x =
        ∑ x ∈ range D.P.ch, kp D tb L0 z zh l x * AYU D t w l (h * D.P.ch + x) zh :=
      sum_congr rfl fun x hx => by rw [AYU_split D t w l zh h (mem_range.mp hx)]
    rw [e2, ← head_swap D t tb L0 w z zh C l h, mul_sum]
    refine sum_congr rfl fun x hx => ?_
    have hx' := mem_range.mp hx
    have m1 : (h * D.P.ch + x) % D.P.ch = x := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hx']
    rw [ew_QK_split D C z hh hx', m1, mul_assoc]
    congr 1
    congr 1
    by_cases hx2 : x % 2 = 0
    · rw [if_pos hx2, if_pos hx2, Nat.add_assoc]
    · have h1 : 1 ≤ x := by omega
      rw [if_neg hx2, if_neg hx2, Nat.add_sub_assoc h1]
  rw [sum_congr rfl fun h hh => e1 h (mem_range.mp hh)]
  -- the order of the sums
  simp only [mul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun h _ => ?_
  conv_rhs => rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun j _ => by ring

/-- The share of the panel QK, at the true contractions of the cells at the end point. -/
theorem share_QK (C : D.ChOK) (H1 H2 : ℕ → ℕ → K)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk)) :
    Pan.QK.share D (rdTrue D t z zh H1 H2) tb L0 w z zh =
      wc D z 2 * ∑ l ∈ range D.nl, el D z 2 l * termHat D t tb L0 w z .QK l zh := by
  show wc D z 2 * ∑ l ∈ range D.nl, Inst.Model.Site.scl (D.Pl l).kq (el D z 2 l) *
    ∑ j ∈ range D.d, valU D t .a l j zh * ∑ h ∈ range (D.P.nq + D.P.nkv),
      ∑ x ∈ range D.P.ch, AH D z h * kp D tb L0 z zh l x * Wqk D w l j h x = _
  congr 1
  refine sum_congr rfl fun l hl => ?_
  rw [hat_QK D t tb L0 w z zh C (hk l (mem_range.mp hl)), Inst.Model.Site.scl_mul,
    Inst.Model.Site.mul_scl]

end Hat

#print axioms pair_swap
#print axioms ew_QK_split
#print axioms AYU_split
#print axioms hat_QK
#print axioms share_QK

end Cb.Pv.Lay.End.Sig
