-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAttAgree.lean: the keys and identities of the attention segment read valid names only.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean).

A trace is a function on the names of cells (`Raw`, Inst/Model/Att/Trace.lean); `Raw.Valid` says
which names are cells. Over any commutative ring: two traces that agree on the valid names of cells
(`Agree`, Cm/SegAttKeyKit.lean) have the same key vectors, at every index, and the same identities,
at every valid name of an identity. Cm/SegAttOK.lean takes from these, at R = ℤ, the statements
`Spec.keyVec_agree` and `Spec.idnVal_agree`, which Cm/TargetSegAtt.lean takes as hypotheses.

Main names:
  `twoFam_agree`: a vector of two families of pieces depends on the families at b < nb and inner
    indices inside the pieces only.
  `keyVec_agree`, `idnVal_agree`: the two statements above.

Why: the model's conditions are formed at a trace that is given on valid names; the families of the
segment read matrices at the places of valid names. The two are compared through these lemmas.
Limits: this file says nothing on tables, bounds or protocols.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegAttKeySum

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.AttSeg (Raw Reg)

variable {R : Type} [CommRing R]

theorem twoFam_agree {nb l l' : ℕ} {f f' k k' : ℕ → ℕ → R} (pad : R)
    (h : ∀ b < nb, ∀ y < 2 ^ l, f b y = k b y)
    (h' : ∀ b < nb, ∀ y < 2 ^ l', f' b y = k' b y) (X : ℕ) :
    AttSeg.twoFam nb l l' f f' pad X = AttSeg.twoFam nb l l' k k' pad X := by
  unfold AttSeg.twoFam
  split_ifs with h1 h2
  · exact h _ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])) _ (Nat.mod_lt _ (Nat.two_pow_pos l))
  · exact h' _ (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm (2 ^ l')]; exact h2))
      _ (Nat.mod_lt _ (Nat.two_pow_pos l'))
  · rfl

theorem attBlk_le {i : ℕ} (hi : i < DA.T) : DA.B * (i / DA.B + 1) ≤ DA.T := by
  have h1 : i / DA.B < DA.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  have h2 : DA.T = DA.B * DA.nBlk := by decide
  rw [h2]
  exact Nat.mul_le_mul_left _ h1

section
variable {t t' : Raw → R} (H : Agree t t') {ρ : Reg} {b x h i j n : ℕ}
include H

theorem attSc_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hj : j < DA.T) :
    ∑ n ∈ range DA.ch, AttSeg.qryV t b h i n * AttSeg.keyV t (DA.lamOf b) h j n =
      ∑ n ∈ range DA.ch, AttSeg.qryV t' b h i n * AttSeg.keyV t' (DA.lamOf b) h j n :=
  sum_congr rfl fun n hn => by
    rw [qry_agree H hb hh hi (mem_range.1 hn), key_agree H (lam_lt hb) hh hj (mem_range.1 hn)]

theorem wtIJ_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    AttSeg.wtIJ DA t b h i j = AttSeg.wtIJ DA t' b h i j := by
  have hI : i / DA.B < DA.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  unfold AttSeg.wtIJ
  split_ifs with hJ
  · have hs := DA.slot_of_blk hJ hI
    exact wt_agree H hb
      (DA.codeM_lt hh hs.1 (lt_of_lt_of_le hs.2.1 (Nat.sub_le _ _))
        (Nat.mod_lt _ DA.B_pos) (Nat.mod_lt _ DA.B_pos))
  · exact wt_agree H hb (DA.codeD_lt hh hI (Nat.mod_lt _ DA.B_pos) (Nat.mod_lt _ DA.B_pos))

theorem RE_agree (u0 : ℕ) (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.RE (DU u0) t b h i n = AttSeg.RE (DU u0) t' b h i n := by
  rw [RE_eq u0 t b h n hi, RE_eq u0 t' b h n hi, den_agree H hb hh hi, out_agree H hb hh hi hn]
  congr 3
  exact sum_congr rfl fun j hj => by
    rw [wtIJ_agree H hb hh hi,
      val_agree H (lam_lt hb) hh (lt_of_lt_of_le (mem_range.1 hj) (attBlk_le hi)) hn]

theorem key1_agree (hb : b < DA.nb) (hx : x < 2 ^ DA.lReg ρ) :
    AttSeg.key1 t ρ b x = AttSeg.key1 t' ρ b x := by
  unfold AttSeg.key1
  rw [r0_agree H hb hx, r1_agree H hb hx, fl_agree H hb hx]

theorem key2M_agree [scl : Scl] (u0 : ℕ) (hb : b < DA.nb) (hx : x < 2 ^ DA.lM) :
    AttSeg.key2 (DU u0) t .M b x = AttSeg.key2 (DU u0) t' .M b x := by
  have hx' : x < 2 ^ DA.lReg .M := hx
  rw [key2M_eq, key2M_eq, rm_agree H hb hx', fl_agree H hb hx', wt_agree H hb hx']
  by_cases he : DA.EmptyM x
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he, mx_agree H hb (DA.mG_lt hx) (iM_lt he),
      attSc_agree H hb (DA.mG_lt hx) (iM_lt he) (jM_lt he)]

theorem key2D_agree [scl : Scl] (u0 : ℕ) (hb : b < DA.nb) (hx : x < 2 ^ DA.lD) :
    AttSeg.key2 (DU u0) t .D b x = AttSeg.key2 (DU u0) t' .D b x := by
  have hx' : x < 2 ^ DA.lReg .D := hx
  rw [key2D_eq, key2D_eq, rm_agree H hb hx', fl_agree H hb hx', wt_agree H hb hx',
    mx_agree H hb (DA.dG_lt hx) (iD_lt x), attSc_agree H hb (DA.dG_lt hx) (iD_lt x) (jD_lt x)]

theorem key3W_agree (u0 χ : ℕ) (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.key3W (DU u0) t χ b h i n = AttSeg.key3W (DU u0) t' χ b h i n := by
  unfold AttSeg.key3W
  rw [RE_agree H u0 hb hh hi hn, qh_agree H hb hh hi hn,
    qh'_agree H hb hh hi hn, den_agree H hb hh hi]

theorem key3X_agree (u0 : ℕ) (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    AttSeg.key3X (DU u0) t b h i = AttSeg.key3X (DU u0) t' b h i := by
  unfold AttSeg.key3X
  congr 2
  exact sum_congr rfl fun k hk => by rw [ib_agree H (mem_range.1 hk) hb hh hi]

theorem key4_agree (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) (hn : n < DA.ch) :
    AttSeg.key4 t b h i n = AttSeg.key4 t' b h i n := by
  unfold AttSeg.key4
  rw [qh_agree H hb hh hi hn, qh'_agree H hb hh hi hn]

/-- The key vectors of traces that agree on the valid names are equal, at every index. -/
theorem keyVec_agree [scl : Scl] (u0 : ℕ) (tb : Tables) :
    ∀ (c : Fin 4) (X : ℕ), AttSeg.keyVec (DU u0) tb t c X = AttSeg.keyVec (DU u0) tb t' c X
  | 0, X => by
    rw [keyVec0, keyVec0]
    exact twoFam_agree _ (fun b hb x hx => key1_agree H (ρ := .M) hb hx)
      (fun b hb x hx => key1_agree H (ρ := .D) hb hx) X
  | 1, X => by
    rw [keyVec1, keyVec1]
    exact twoFam_agree _ (fun b hb x hx => key2M_agree H u0 hb hx)
      (fun b hb x hx => key2D_agree H u0 hb hx) X
  | 2, X => by
    rw [keyVec2, keyVec2]
    refine twoFam_agree _ (fun b hb y _ => key3W_agree H u0 _ hb (wH_lt y) (wI_lt y) (wN_lt y))
      (fun b hb y hy => key3X_agree H u0 hb (Nat.div_lt_of_lt_mul ?_) (Nat.mod_lt _ (by decide))) X
    have h2 : (2 : ℕ) ^ DA.lX = DA.T * DA.nG := by decide
    have hy' : y < 2 ^ DA.lX := hy
    show y < DA.T * DA.nG
    omega
  | 3, X => by
    rw [keyVec3, keyVec3]
    refine twoFam_agree _
      (fun b hb y hy => key4_agree H hb ?_ (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))
      (fun _ _ _ _ => rfl) X
    show y / DA.ch / DA.T < DA.nG
    rw [Nat.div_div_eq_div_mul]
    refine Nat.div_lt_of_lt_mul ?_
    have h2 : (2 : ℕ) ^ DA.l4 = DA.ch * DA.T * DA.nG := by decide
    have hy' : y < 2 ^ DA.l4 := hy
    omega

/-- The identities of traces that agree on the valid names are equal, at every valid name of an
identity. -/
theorem idnVal_agree {j : AttSeg.Idn} (hj : j.Valid DA) :
    AttSeg.idnVal DA t j = AttSeg.idnVal DA t' j := by
  cases j with
  | at1 k b g i =>
    obtain ⟨hk, hb, hg, hi⟩ := hj
    show AttSeg.ibV t k b g i * (AttSeg.ibV t k b g i - 1) =
      AttSeg.ibV t' k b g i * (AttSeg.ibV t' k b g i - 1)
    rw [ib_agree H hk hb hg hi]
  | at2 b g i =>
    obtain ⟨hb, hg, hi⟩ := hj
    show AttSeg.mxV t b g i - ∑ n ∈ range DA.ch, AttSeg.qryV t b g i n * AttSeg.sel DA t b g i n =
      AttSeg.mxV t' b g i - ∑ n ∈ range DA.ch, AttSeg.qryV t' b g i n * AttSeg.sel DA t' b g i n
    rw [mx_agree H hb hg hi]
    refine congrArg (AttSeg.mxV t' b g i - ·) (sum_congr rfl fun n hn => ?_)
    rw [qry_agree H hb hg hi (mem_range.1 hn)]
    refine congrArg (AttSeg.qryV t' b g i n * ·) ?_
    unfold AttSeg.sel
    refine sum_congr rfl fun j hj => ?_
    rw [key_agree H (lam_lt hb) hg (mem_range.1 hj) (mem_range.1 hn)]
    refine congrArg (AttSeg.keyV t' (DA.lamOf b) g j n * ·) ?_
    exact prod_congr rfl fun k hk => by rw [ib_agree H (mem_range.1 hk) hb hg hi]
  | at3 b g i =>
    obtain ⟨hb, hg, hi⟩ := hj
    show AttSeg.denV t b g i - AttSeg.rowSum DA t (fun _ => 1) b g i =
      AttSeg.denV t' b g i - AttSeg.rowSum DA t' (fun _ => 1) b g i
    rw [den_agree H hb hg hi, AttSeg.rowSum_eq DA t _ b g hi, AttSeg.rowSum_eq DA t' _ b g hi]
    exact congrArg (AttSeg.denV t' b g i - ·)
      (sum_congr rfl fun j _ => by rw [wtIJ_agree H hb hg hi])

end
end Cm.Seg
