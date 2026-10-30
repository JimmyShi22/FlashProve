-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/TnSplit.lean: the tensor claims of a feed-forward segment's weight panels as pairs of
coefficients on the rows and on the columns of the committed matrix.

Cb/Pv/Lay/At/TnLib.lean gives, for each row of a weight panel, a tensor claim tnOf on the matrix W
whose functional is the library's value of the panel's row (Pan.TnRow, Pan.TnPan).
Inst/Model/LayoutSplit.lean shows that a claim whose factors are given by descriptions that fit the
unit's coordinates (FD, AllOK) is a claim of the library's merge: a pair (γ, ε). This file gives the
descriptions of the factors of tnOf, shows that they fit, and concludes that the value of the pair
(tval in Cb/Pv/Lay/At/FootW.lean) is the library's value of the panel's row.

Main names.
  dsOf: the descriptions of the factors of tnOf. tnOf_f: they are its factors.
  aligned_pos: the library's map from a family's indices to columns is aligned, as a coordinate of
    kind high asks, also from an aligned index on.
  allOK_dsOf: the descriptions fit.
  pairOf, tval_pairOf: the pair of a claim that is given by descriptions, and its value.
  tenAt: the pair of row ρ of the panel p. tenAt_row, tenAt_pan: its value on the matrix is
    Pan.TnRow, for a panel with three factors Pan.TnPan, at the weights that the layout reads in W.

The hypotheses: L0 is even; a layer has twice an expert's hidden units; at most 64 heads; the row's
layer is a layer of the model; the matrix has room for all units.

Limits. Nothing on the panels without weights, on the embedding or on the output matrix. That the
programs' coefficients are these is not said.


-/
import Cb.Pv.Lay.At.TnLib
import Cb.Pv.Lay.At.FootW
import Inst.Model.LayoutSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At

open Finset
open Inst.Model (Params Tables)
open Inst.Model.Layout (sOf units off rows UnitS)
open Inst.Model.Layout.Tensor (FD AllOK Aligned gsOf rsOf lunit matOf Tn_eq_tlay_of rows_fit facCOf
  facROf two_pow_sOf_dvd sOf_le_of_le)
open Inst.Model.FFSeg (Dim Pan Rd layerR lamS lJ call zc pos len used AH kp fSh isExpL)
open Inst.Model.FFSeg.IndexFacts (posAligned mem_fams_call used_le)

noncomputable section

variable {K : Type} [Field K]

/-! ### The map from indices to columns -/

/-- A member's share is at most the sum. -/
theorem le_sum_map {α : Type} (f : α → ℕ) : ∀ (l : List α) (x : α), x ∈ l → f x ≤ (l.map f).sum
  | [], _, h => by cases h
  | y :: l, x, h => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with e | h'
    · rw [e]
      exact Nat.le_add_right _ _
    · exact Nat.le_trans (le_sum_map f l x h') (Nat.le_add_left _ _)

/-- A family's indices fit the columns of its call. -/
theorem len_le (D : Dim) (s : Inst.Model.FFSeg.Fam) : len D s ≤ 2 ^ lJ D (call s) :=
  le_trans (le_sum_map (len D) _ s (mem_fams_call s)) (used_le D (call s))

/-- The map from a family's indices to columns, from an aligned index base on, is aligned. -/
theorem aligned_pos (D : Dim) (s : Inst.Model.FFSeg.Fam) (R base : ℕ) (hb : 2 ^ sOf R ∣ base)
    (hl : 2 ^ sOf R ∣ len D s) (hle : base + R ≤ len D s) :
    Aligned (sOf R) R fun x => pos D s (base + x) := by
  intro i hi
  obtain ⟨q, rfl⟩ := hb
  have hdm := Nat.div_add_mod i (2 ^ sOf R)
  have e1 : 2 ^ sOf R * q + i = 2 ^ sOf R * (q + i / 2 ^ sOf R) + i % 2 ^ sOf R := by
    rw [Nat.mul_add]
    omega
  have e2 : 2 ^ sOf R * q + i / 2 ^ sOf R * 2 ^ sOf R = 2 ^ sOf R * (q + i / 2 ^ sOf R) := by
    rw [Nat.mul_add, Nat.mul_comm (i / 2 ^ sOf R)]
  have hx : 2 ^ sOf R * (q + i / 2 ^ sOf R) < len D s := by omega
  obtain ⟨a1, a2⟩ := posAligned D s (sOf R) (q + i / 2 ^ sOf R) (i % 2 ^ sOf R) hl hx
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  show pos D s (2 ^ sOf R * q + i) =
      pos D s (2 ^ sOf R * q + i / 2 ^ sOf R * 2 ^ sOf R) + i % 2 ^ sOf R ∧
    2 ^ sOf R ∣ pos D s (2 ^ sOf R * q + i / 2 ^ sOf R * 2 ^ sOf R)
  rw [e2, e1]
  exact ⟨a1, a2⟩

/-- The same from the index 0 on. -/
theorem aligned_pos0 (D : Dim) (s : Inst.Model.FFSeg.Fam) (R : ℕ) (hl : 2 ^ sOf R ∣ len D s)
    (hle : R ≤ len D s) : Aligned (sOf R) R (pos D s) := by
  intro i hi
  have h := aligned_pos D s R 0 (Nat.dvd_zero _) hl (by omega) i hi
  simpa only [Nat.zero_add] using h

/-- The bits that a coordinate of at most as many indices as the family has can give to the columns
are at most the bits of a column of the call. -/
theorem sOf_le_lJ (D : Dim) (s : Inst.Model.FFSeg.Fam) (R : ℕ) (hle : R ≤ len D s) :
    sOf R ≤ lJ D (call s) := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · exact Nat.zero_le _
  · exact sOf_le_of_le hR (le_trans hle (len_le D s))

/-! ### The descriptions -/

section Descr

variable (D : Dim) (tb : Tables) (L0 : ℕ) (z zh ζ : ℕ → K)

/-- The equality weights of a panel's columns, as a description. -/
def dEc (p : Pan) : FD K := .low (p.wcol D) (lamS D - p.wcol D) ζ
/-- Those of its rows. -/
def dEr (p : Pan) : FD K := .low (p.wid D - p.wcol D) (lamS D - p.wid D) ζ
/-- Those of a family's entries at the lookup's point. -/
def dEw (s : Inst.Model.FFSeg.Fam) : FD K := .high (lJ D (call s)) D.lL (zc D z (call s)) (pos D s)

/-- The descriptions of the factors of tnOf. -/
def dsOf : Pan → ℕ → List (FD K)
  | .G, _ => [dEc D ζ .G, dEw D z .G]
  | .U, _ => [dEc D ζ .U, dEw D z .U]
  | .V, _ => [dEc D ζ .V, dEw D z .V]
  | .O, _ => [dEc D ζ .O, dEw D z .O]
  | .D, _ => [dEc D ζ .D, dEw D z .D]
  | .LR, _ => [dEc D ζ .LR, dEw D z .LR]
  | .QK, l => [.whole fun h => if h < D.P.nq + D.P.nkv then AH D z h else 0,
      .whole (kp D tb L0 z zh l), dEc D ζ .QK]
  | .Gr l', _ => [dEc D ζ (.Gr l'), dEr D ζ (.Gr l'),
      .high (lJ D (call .G)) D.lL (zc D z (call .G)) fun x => pos D .G (D.fe + x)]
  | .Ur l', _ => [dEc D ζ (.Ur l'), dEr D ζ (.Ur l'),
      .high (lJ D (call .U)) D.lL (zc D z (call .U)) fun x => pos D .U (D.fe + x)]
  | .Dr l', _ => [dEc D ζ (.Dr l'), dEr D ζ (.Dr l'), dEw D z .D]
  | _, _ => []

/-- They are the factors of tnOf. -/
theorem tnOf_f (p : Pan) (ρ : ℕ) :
    (tnOf D tb L0 z zh ζ p ρ).f = (dsOf D tb L0 z zh ζ p ρ).map FD.f := by
  cases p <;> rfl

/-- The claim tnOf, with its factors given by the descriptions. -/
theorem tnOf_eq (p : Pan) (ρ : ℕ) :
    tnOf D tb L0 z zh ζ p ρ = ⟨(tnOf D tb L0 z zh ζ p ρ).n, (tnOf D tb L0 z zh ζ p ρ).U,
      (dsOf D tb L0 z zh ζ p ρ).map FD.f⟩ := by
  cases p <;> rfl

/-- The hidden units of a layer that are not routed divide the hidden units of a layer. -/
theorem fSh_dvd (hf : D.f = 2 * D.fe) (l : ℕ) : fSh D l ∣ D.f := by
  unfold Inst.Model.FFSeg.fSh
  split_ifs
  · exact ⟨2, by rw [hf, Nat.mul_comm]⟩
  · exact dvd_refl _

theorem fSh_le (hf : D.f = 2 * D.fe) (l : ℕ) : fSh D l ≤ D.f := by
  unfold Inst.Model.FFSeg.fSh
  split_ifs
  · omega
  · exact le_refl _

omit [Field K] in
/-- A coordinate of kind high with all of a family's indices. -/
theorem ew_fits (s : Inst.Model.FFSeg.Fam) (R : ℕ) (hl : R ∣ len D s) (hle : R ≤ len D s) :
    (dEw D z s).OK ⟨R, .high⟩ :=
  ⟨rfl, sOf_le_lJ D s R hle, aligned_pos0 D s R (dvd_trans (two_pow_sOf_dvd R) hl) hle⟩

omit [Field K] in
/-- A coordinate of kind low with at most as many indices as the panel has columns. -/
theorem ec_fits (p : Pan) (R : ℕ) (h : R ≤ p.nc D) : (dEc D ζ p).OK ⟨R, .low⟩ :=
  ⟨rfl, le_trans h (Nat.le_pow_clog (by norm_num) _)⟩

omit [Field K] in
/-- A coordinate of kind low with at most as many indices as the panel has rows. -/
theorem er_fits (p : Pan) (R : ℕ) (h : R ≤ p.nr D) : (dEr D ζ p).OK ⟨R, .low⟩ := by
  refine ⟨rfl, le_trans h ?_⟩
  show p.nr D ≤ 2 ^ (Nat.clog 2 (p.nr D) + p.wcol D - p.wcol D)
  rw [Nat.add_sub_cancel]
  exact Nat.le_pow_clog (by norm_num) _

omit [Field K] in
/-- The routed half of a family with f indices. -/
theorem routed_fits (hf : D.f = 2 * D.fe) (s : Inst.Model.FFSeg.Fam) (hs : len D s = D.f) :
    (FD.high (lJ D (call s)) D.lL (zc D z (call s)) fun x => pos D s (D.fe + x) : FD K).OK
      ⟨D.P.fe, .high⟩ := by
  have h1 : D.P.fe ≤ len D s := by
    rw [hs, hf]
    show D.fe ≤ 2 * D.fe
    omega
  have h2 : D.fe + D.P.fe ≤ len D s := by
    rw [hs, hf]
    show D.fe + D.fe ≤ 2 * D.fe
    omega
  refine ⟨rfl, sOf_le_lJ D s D.P.fe h1,
    aligned_pos D s D.P.fe D.fe (two_pow_sOf_dvd _) ?_ h2⟩
  rw [hs, hf]
  exact dvd_trans (two_pow_sOf_dvd _) ⟨2, Nat.mul_comm 2 D.fe⟩

/-- The descriptions fit the coordinates of the claim's unit. -/
theorem allOK_dsOf (hf : D.f = 2 * D.fe) (p : Pan) (ρ : ℕ) :
    AllOK (tnOf D tb L0 z zh ζ p ρ).U.coords (dsOf D tb L0 z zh ζ p ρ) := by
  cases p with
  | G => exact ⟨ec_fits D ζ .G _ (le_refl _),
      ew_fits D z .G _ (fSh_dvd D hf ρ) (fSh_le D hf ρ), trivial⟩
  | U => exact ⟨ec_fits D ζ .U _ (le_refl _),
      ew_fits D z .U _ (fSh_dvd D hf ρ) (fSh_le D hf ρ), trivial⟩
  | V => exact ⟨ec_fits D ζ .V _ (le_refl _), ew_fits D z .V _ (dvd_refl _) (le_refl _), trivial⟩
  | O => exact ⟨ec_fits D ζ .O _ (le_refl _), ew_fits D z .O _ (dvd_refl _) (le_refl _), trivial⟩
  | D => exact ⟨ec_fits D ζ .D _ (fSh_le D hf ρ),
      ew_fits D z .D _ (dvd_refl _) (le_refl _), trivial⟩
  | LR => exact ⟨ec_fits D ζ .LR _ (le_refl _),
      ew_fits D z .LR _ (dvd_refl _) (le_refl _), trivial⟩
  | QK => exact ⟨rfl, rfl, ec_fits D ζ .QK _ (le_refl _), trivial⟩
  | Gr l' => exact ⟨ec_fits D ζ (.Gr l') _ (le_refl _), er_fits D ζ (.Gr l') _ (le_refl _),
      routed_fits D z hf .G rfl, trivial⟩
  | Ur l' => exact ⟨ec_fits D ζ (.Ur l') _ (le_refl _), er_fits D ζ (.Ur l') _ (le_refl _),
      routed_fits D z hf .U rfl, trivial⟩
  | Dr l' => exact ⟨ec_fits D ζ (.Dr l') _ (le_refl _), er_fits D ζ (.Dr l') _ (le_refl _),
      ew_fits D z .D _ (dvd_refl _) (le_refl _), trivial⟩
  | N1 => exact trivial
  | N2 => exact trivial
  | XR => exact trivial
  | DD => exact trivial
  | MR => exact trivial

end Descr

/-! ### The pairs -/

/-- The pair (γ, ε) of the claim on the unit U with the number n whose factors are given by the
descriptions ds, in a matrix of h rows and 2^k columns. -/
def pairOf (P : Params) (k h n : ℕ) (U : UnitS) (ds : List (FD K))
    (hr : off k (units P) n + rows k U ≤ h) : (Fin h → K) × ((Fin k → Bool) → K) :=
  (lunit k h (units P) n U hr).toTLay.toTen
    (Blocks.Layout.prodC _ (facCOf _ (gsOf U.coords k ds)))
    (Blocks.Layout.prodR _ (facROf _ (rsOf U.coords k ds)))

/-- Its value on the matrix is the claim's functional. -/
theorem tval_pairOf (P : Params) (k h n : ℕ) (U : UnitS) (ds : List (FD K))
    (hr : off k (units P) n + rows k U ≤ h) (hd : AllOK U.coords ds) (W : ℕ → ℕ → K) :
    tval (pairOf P k h n U ds hr) (matOf W) =
      (⟨n, U, ds.map FD.f⟩ : Inst.Model.TClaim K).Tn P k W := by
  rw [Tn_eq_tlay_of P k h W n U ds hr hd, Blocks.MG.TLay.Tn_eq]
  rfl

section At

variable (D : Dim) (tb : Tables) (L0 k h : ℕ) (z zh ζ : ℕ → K)

open Classical in
/-- The pair of row ρ of the weight panel p (of the panel, if it has three factors). If the matrix
has no room for the unit: zero. -/
def tenAt (p : Pan) (ρ : ℕ) : (Fin h → K) × ((Fin k → Bool) → K) :=
  if hr : off k (units D.P) (tnOf D tb L0 z zh ζ p ρ).n + rows k (tnOf D tb L0 z zh ζ p ρ).U ≤ h
  then pairOf D.P k h _ _ (dsOf D tb L0 z zh ζ p ρ) hr
  else (0, 0)

variable {L0}

/-- The pair's value on the matrix is the functional of the claim tnOf. -/
theorem tenAt_Tn (h0 : L0 % 2 = 0) (hf : D.f = 2 * D.fe) (p : Pan) (hw : p.weight = true) (ρ : ℕ)
    (hL : L0 + layerOfRow p ρ < D.P.layers)
    (hH : off k (units D.P) (units D.P).length ≤ h) (W : ℕ → ℕ → K) :
    tval (tenAt D tb L0 k h z zh ζ p ρ) (matOf W) = (tnOf D tb L0 z zh ζ p ρ).Tn D.P k W := by
  have hr := rows_fit k h (units D.P) _ _ (tnOf_unit D tb h0 z zh ζ p hw ρ hL) hH
  unfold tenAt
  rw [dif_pos hr, tval_pairOf D.P k h _ _ _ hr (allOK_dsOf D tb L0 z zh ζ hf p ρ) W,
    ← tnOf_eq D tb L0 z zh ζ p ρ]

/-- For a weight panel with two factors: the pair's value is the library's value of the row. -/
theorem tenAt_row (r : Rd K) (h0 : L0 % 2 = 0) (hf : D.f = 2 * D.fe)
    (hh : D.P.nq + D.P.nkv ≤ 64) (p : Pan) (hw : p.weight = true) (h3 : p.three = false) (ρ : ℕ)
    (hL : L0 + layerOfRow p ρ < D.P.layers)
    (hH : off k (units D.P) (units D.P).length ≤ h) (W : ℕ → ℕ → K) :
    tval (tenAt D tb L0 k h z zh ζ p ρ) (matOf W) =
      p.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ ρ := by
  rw [tenAt_Tn D tb k h z zh ζ h0 hf p hw ρ hL hH W,
    TnRow_Tn D r tb h0 k W z zh ζ (by omega) hh p hw h3 ρ]

/-- For a weight panel with three factors: the pair's value is the library's value of the panel. -/
theorem tenAt_pan (r : Rd K) (h0 : L0 % 2 = 0) (hf : D.f = 2 * D.fe) (p : Pan)
    (hw : p.weight = true) (h3 : p.three = true) (hL : L0 + layerOfRow p 0 < D.P.layers)
    (hH : off k (units D.P) (units D.P).length ≤ h) (W : ℕ → ℕ → K) :
    tval (tenAt D tb L0 k h z zh ζ p 0) (matOf W) =
      p.TnPan D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ := by
  rw [tenAt_Tn D tb k h z zh ζ h0 hf p hw 0 hL hH W, TnPan_Tn D r tb h0 k W z zh ζ p h3]

end At

end

end Cb.Pv.Lay.At
