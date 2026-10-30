-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysW.lean: the forms of the segments O, LR, G and U plus the matrix products in
their keys; the matrix products in the keys of D; and what the verifier's panels of O, LR, G and U
hold.

The library cuts a key in three parts: key = lin + term + mat (Inst/Model/FF/Objects.lean, key_eq).
The verifier's form of a segment is worth the part lin (Johnson/Road/FormsKeysA.lean and its
sisters). The part mat, a product of a vector of values with a weight matrix under the factor
2^max(0, 16 - k) of the rounding's shift k, is left to a panel of the batched sumcheck
(OnBytes/Model/LayerPanels.lean). This file has three kinds of statements.
 - acc_X: the parts mat of the family X at one layer, summed under any weights g, written on the
   library's own objects in the shape in which a row of a panel would hold them: the factor, times
   the sum over j of the extension of a vector of values at the token point, times the sum over the
   segment's entries x of g x times the matrix's entry at (j, x).
 - whole_X: the value of the segment's form plus that sum is the weighted sum of the extensions of
   the whole keys. This is stated where the part term is 0: for O, for LR, and for G and U on a
   layer without routed experts.
 - panelX_spec: what the verifier's panelA appends for the segment X, against the library's panel
   Pan.X: rows, columns, the first weight claim, what the A side is worth, the weight of each row.

No panel of the verifier stands in a statement of the first two kinds, and no theorem here adds a
panel of the verifier to a form. The third kind says that the A side and the rows' weights of the
verifier's panel are worth the first factor and the factor 2^max(0, 16 - k) of the first kind. Of no
panel is the B side compared: it is a weight matrix, for which the panel leaves weight claims. The
library's weight of a row (Pan.wt) holds the layer's weight at the library's own point; here the
layer's weight is left free.

The hidden units of a layer. On a layer with routed experts the part mat of G and of U is 0 from
hidden unit fe on, and the sum in the part mat of D ends at fe. The library's fSh is fe on such a
layer and f on any other. acc_G, acc_U and acc_D are stated with fSh; acc_G_even, acc_G_odd,
acc_U_even and acc_U_odd say the same with f and with fe.

The first factor in acc_D is a vector that the prover never sends: for each hidden unit the gated
product, summed over the positions under the equality weights of the token point. acc_D is stated on
the library's name for it, hhU. There is no statement on the verifier's panel of D.

The attention output. The record Fits does not fix the profile: its switch p3 holds at profile 3,
and at profile 4 with routed experts. At profile 4 the A side of the verifier's panel of O reads the
array o. No segment's form reads that array, so the record does not speak of it: panelO_spec asks
that the profile is 4 and that the array is found, tied and true at the token point (HasShort). At
profile 3 the A side is a public number and the layout has no tensor for o: panelO_spec does not
apply, and whole_O, which is stated on the library's cells of o, says nothing of the verifier's
panel.

Main theorems: wsum_scl_matrix; acc_O, acc_LR, acc_G, acc_U, acc_D; Fits.whole_O, Fits.whole_LR,
Fits.whole_G_even, Fits.whole_U_even; panelO_spec, panelLR_spec, panelG_spec, panelU_spec.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. That the sumcheck shows a panel's sum, that
the weight claims which a panel leaves say what the B side stands for, and that the never-sent
vector is the gated product, is not touched. Nothing is said on the part term of G, U and D on a
layer with routed experts. The program does not import this file.
-/
import Johnson.Road.FormsKeysA
import Johnson.Road.FormsKeysB
import Johnson.Road.FormsKeysD
import OnBytes.Model.LayerPanels

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env SBlk Panels PanelEnv panelA)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin term mat len valU hhU fSh routed isExpL Pan Rd)

/-! ## Tools -/

section Tools

variable {K : Type} [Field K]

/-- Products of a vector a with the columns of a matrix M, each under the factor of the shift k,
summed under weights g: the factor times the sum over j of the extension of a j times the sum of row
j of M under g. -/
theorem wsum_scl_matrix (g : ℕ → K) (lt : ℕ) (u : ℕ → K) (n m k : ℕ) (a M : ℕ → ℕ → K) :
    wsum g lt u n (fun x i => Inst.Model.Site.scl k (∑ j ∈ range m, a j i * M j x)) =
      Inst.Model.Site.scl k
        (∑ j ∈ range m, Blocks.ext lt (a j) u * ∑ x ∈ range n, g x * M j x) := by
  have e : ∀ x, Blocks.ext lt
      (fun i => (2 : K) ^ Inst.Model.Site.dn k * ∑ j ∈ range m, a j i * M j x) u =
      (2 : K) ^ Inst.Model.Site.dn k * ∑ j ∈ range m, Blocks.ext lt (a j) u * M j x := by
    intro x
    rw [Blocks.ext_smul, Blocks.ext_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have c : (fun i => a j i * M j x) = fun i => M j x * a j i := by
      funext i
      ring
    rw [c, Blocks.ext_smul]
    ring
  unfold wsum
  simp only [Inst.Model.Site.scl_eq]
  simp only [e]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  refine sum_congr rfl fun x _ => ?_
  ring

/-- For an array without an offset, what the cells spell is the library's value. -/
theorem ext_raw (D : Dim) (t : Cell → K) (u : ℕ → K) {X : Arr} (hX : X.off = 0) (i j : ℕ) :
    Blocks.ext D.lT (raw t X i j) u = valU D t X i j u := by
  unfold valU
  congr 1
  funext p
  simp [raw, hX]

/-- A weight under the verifier's factor of the shift k reads as the library's. -/
theorem scl_weight {ρ : Reading K} (hρ : Numerals ρ) (e : E) (k : ℕ) :
    ρ.val (mulE e (Model.Layer.pw (Model.Layer.tOf k))) = Inst.Model.Site.scl k (ρ.val e) := by
  rw [ρ.mul, Inst.Model.Site.scl_eq, hρ.pw]
  unfold Model.Layer.tOf Inst.Model.Site.dn
  ring

end Tools

/-- Member i of the array of the values of fn at 0 to n - 1. -/
theorem range_map_getD (n : ℕ) (fn : ℕ → E) {i : ℕ} (hi : i < n) :
    ((Array.range n).map fn).getD i zeroE = fn i := by
  simp [Array.getD, hi]

/-- On a layer without routed experts all f hidden units are shared. -/
theorem fSh_even (D : Dim) {l : ℕ} (hl : l % 2 = 0) : fSh D l = D.f := by
  simp [fSh, isExpL, hl]

/-- On a layer with routed experts the first fe hidden units are shared. -/
theorem fSh_odd (D : Dim) {l : ℕ} (hl : l % 2 = 1) : fSh D l = D.fe := by
  simp [fSh, isExpL, hl]

/-- A shared hidden unit does not belong to the routed expert. -/
theorem routed_false (D : Dim) {l x : ℕ} (hx : x < fSh D l) : routed D l x = false := by
  unfold fSh at hx
  unfold routed
  cases h : isExpL l with
  | false => rfl
  | true =>
    rw [h] at hx
    have hx' : x < D.fe := hx
    simpa using hx'

/-! ## The matrix products of a family at one layer, under free weights -/

section Acc

variable {K : Type} [Field K] [scl : Scl] (D : Dim) (t : Cell → K) (w : ℕ → LW K) (g u : ℕ → K)

/-- O: the attention output o[l] with the matrix Wo. -/
theorem acc_O (l : ℕ) :
    wsum g D.lT u D.d (fun x i => mat D t w .O l x i) =
      Inst.Model.Site.scl (D.Pl l).ko
        (∑ j ∈ range D.dq, valU D t .o l j u * ∑ x ∈ range D.d, g x * (w l).Wo j x) :=
  wsum_scl_matrix g D.lT u D.d D.dq (D.Pl l).ko (fun j i => Inst.Model.FFSeg.val t .o l j i)
    (fun j x => (w l).Wo j x)

/-- LR: the array m[l] with the router's matrix Wr. -/
theorem acc_LR (l : ℕ) :
    wsum g D.lT u D.nx (fun x i => mat D t w .LR l x i) =
      Inst.Model.Site.scl (D.Pl l).kr
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range D.nx, g x * (w l).Wr j x) :=
  wsum_scl_matrix g D.lT u D.nx D.d (D.Pl l).kr (fun j i => Inst.Model.FFSeg.val t .m l j i)
    (fun j x => (w l).Wr j x)

/-- G: the array m[l] with the gate's matrix Wg, over the shared hidden units. -/
theorem acc_G (l : ℕ) :
    wsum g D.lT u (fSh D l) (fun x i => mat D t w .G l x i) =
      Inst.Model.Site.scl (D.Pl l).kg
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range (fSh D l), g x * (w l).Wg j x) := by
  have e : ∀ x, x < fSh D l → ∀ i, mat D t w .G l x i = Inst.Model.Site.scl (D.Pl l).kg
      (∑ j ∈ range D.d, Inst.Model.FFSeg.val t .m l j i * (w l).Wg j x) := by
    intro x hx i
    simp only [mat, Inst.Model.FFSeg.Ag, routed_false D hx, Bool.false_eq_true, if_false]
  rw [wsum_congr _ _ _ _ e]
  exact wsum_scl_matrix g D.lT u (fSh D l) D.d (D.Pl l).kg
    (fun j i => Inst.Model.FFSeg.val t .m l j i) (fun j x => (w l).Wg j x)

/-- U: the array m[l] with the matrix Wu, over the shared hidden units. -/
theorem acc_U (l : ℕ) :
    wsum g D.lT u (fSh D l) (fun x i => mat D t w .U l x i) =
      Inst.Model.Site.scl (D.Pl l).ku
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range (fSh D l), g x * (w l).Wu j x) := by
  have e : ∀ x, x < fSh D l → ∀ i, mat D t w .U l x i = Inst.Model.Site.scl (D.Pl l).ku
      (∑ j ∈ range D.d, Inst.Model.FFSeg.val t .m l j i * (w l).Wu j x) := by
    intro x hx i
    simp only [mat, Inst.Model.FFSeg.Au, routed_false D hx, Bool.false_eq_true, if_false]
  rw [wsum_congr _ _ _ _ e]
  exact wsum_scl_matrix g D.lT u (fSh D l) D.d (D.Pl l).ku
    (fun j i => Inst.Model.FFSeg.val t .m l j i) (fun j x => (w l).Wu j x)

/-- G on a layer without routed experts: all f hidden units. -/
theorem acc_G_even {l : ℕ} (hl : l % 2 = 0) :
    wsum g D.lT u D.f (fun x i => mat D t w .G l x i) =
      Inst.Model.Site.scl (D.Pl l).kg
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range D.f, g x * (w l).Wg j x) := by
  have e := acc_G D t w g u l
  rw [fSh_even D hl] at e
  exact e

/-- G on a layer with routed experts: the first fe hidden units. -/
theorem acc_G_odd {l : ℕ} (hl : l % 2 = 1) :
    wsum g D.lT u D.fe (fun x i => mat D t w .G l x i) =
      Inst.Model.Site.scl (D.Pl l).kg
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range D.fe, g x * (w l).Wg j x) := by
  have e := acc_G D t w g u l
  rw [fSh_odd D hl] at e
  exact e

/-- U on a layer without routed experts: all f hidden units. -/
theorem acc_U_even {l : ℕ} (hl : l % 2 = 0) :
    wsum g D.lT u D.f (fun x i => mat D t w .U l x i) =
      Inst.Model.Site.scl (D.Pl l).ku
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range D.f, g x * (w l).Wu j x) := by
  have e := acc_U D t w g u l
  rw [fSh_even D hl] at e
  exact e

/-- U on a layer with routed experts: the first fe hidden units. -/
theorem acc_U_odd {l : ℕ} (hl : l % 2 = 1) :
    wsum g D.lT u D.fe (fun x i => mat D t w .U l x i) =
      Inst.Model.Site.scl (D.Pl l).ku
        (∑ j ∈ range D.d, valU D t .m l j u * ∑ x ∈ range D.fe, g x * (w l).Wu j x) := by
  have e := acc_U D t w g u l
  rw [fSh_odd D hl] at e
  exact e

/-- D: the gated products of the shared hidden units, as one vector, with the matrix Wd. -/
theorem acc_D (l : ℕ) :
    wsum g D.lT u D.d (fun x i => mat D t w .D l x i) =
      Inst.Model.Site.scl (D.Pl l).kd
        (∑ j ∈ range (fSh D l), hhU D t l j u * ∑ x ∈ range D.d, g x * (w l).Wd j x) :=
  wsum_scl_matrix g D.lT u D.d (fSh D l) (D.Pl l).kd (fun j i => Inst.Model.FFSeg.hh t l j i)
    (fun j x => (w l).Wd j x)

end Acc

/-! ## A form plus the matrix products of its keys -/

section Whole

variable {K : Type} [Field K] [scl : Scl] {ρ : Reading K} {W : World K} {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K}

/-- The family O, whole: the value of the segment's form plus the matrix products of the keys,
written as a row of a panel would hold them, is the weighted sum of the extensions of the library's
keys. The products are those of the library's cells of the attention output o. At profile 3 the
verifier has no such cells, its panel holds public numbers in their place, and this theorem says
nothing of that panel. -/
theorem Fits.whole_O (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (lam : ℕ)
    (hlam : lam < D.nl) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.d) {f : Aff}
    (h : v.line "O" lam ew wh = some f) :
    f.value ρ W + Inst.Model.Site.scl (D.Pl lam).ko
        (∑ j ∈ range D.dq, valU D t .o lam j u * ∑ x ∈ range D.d, wt ρ ew x * (w lam).Wo j x) =
      ∑ x ∈ range (len D .O), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => key D t tb L0 w .O lam x i) u := by
  have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .O lam x i =
      lin D t tb L0 w .O lam x i + mat D t w .O lam x i := by
    intro x _ i
    rw [Inst.Model.FFSeg.key_eq]
    simp [term]
  show _ = wsum (wt ρ ew) D.lT u D.d (fun x i => key D t tb L0 w .O lam x i)
  rw [wsum_congr _ _ _ _ e, wsum_add, acc_O, F.line_O tb L0 w lam hlam hw h]
  rfl

/-- The family LR on an odd layer, whole: the value of the segment's form plus the matrix products
of the keys, written as a row of a panel would hold them. The cells of the quotient and of the
digits are those of instance lam / 2; the vector m is that of layer lam. -/
theorem Fits.whole_LR (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (lam : ℕ)
    (hlam : lam < D.nl) {ew wh : Array E} (hsz : ew.size = len D .LR) (hodd : lam % 2 = 1) {f : Aff}
    (h : v.line "LR" lam ew wh = some f) :
    f.value ρ W + Inst.Model.Site.scl (D.Pl lam).kr
        (∑ j ∈ range D.d, valU D t .m lam j u * ∑ x ∈ range D.nx, wt ρ ew x * (w lam).Wr j x) =
      ∑ x ∈ range (len D .LR), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => key D t tb L0 w .LR lam x i) u := by
  have e : ∀ x, x < D.nx → ∀ i, key D t tb L0 w .LR lam x i =
      lin D t tb L0 w .LR lam x i + mat D t w .LR lam x i := by
    intro x _ i
    rw [Inst.Model.FFSeg.key_eq]
    simp [term]
  show _ = wsum (wt ρ ew) D.lT u D.nx (fun x i => key D t tb L0 w .LR lam x i)
  rw [wsum_congr _ _ _ _ e, wsum_add, acc_LR, F.line_LR tb L0 w lam hlam hsz hodd h]
  rfl

/-- The family G on a layer without routed experts, whole: the value of the segment's form plus the
matrix products of the keys, written as a row of a panel would hold them. -/
theorem Fits.whole_G_even (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (lam : ℕ) (hlam : lam < D.nl) (hl : lam % 2 = 0) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff} (h : v.line "G" lam ew wh = some f) :
    f.value ρ W + Inst.Model.Site.scl (D.Pl lam).kg
        (∑ j ∈ range D.d, valU D t .m lam j u * ∑ x ∈ range D.f, wt ρ ew x * (w lam).Wg j x) =
      ∑ x ∈ range (len D .G), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => key D t tb L0 w .G lam x i) u := by
  have e : ∀ x, x < D.f → ∀ i, key D t tb L0 w .G lam x i =
      lin D t tb L0 w .G lam x i + mat D t w .G lam x i := by
    intro x hx i
    have hr : routed D lam x = false := routed_false D (by rw [fSh_even D hl]; exact hx)
    rw [Inst.Model.FFSeg.key_eq]
    simp [term, hr]
  show _ = wsum (wt ρ ew) D.lT u D.f (fun x i => key D t tb L0 w .G lam x i)
  rw [wsum_congr _ _ _ _ e, wsum_add, acc_G_even D t w (wt ρ ew) u hl,
    F.line_G tb L0 w lam hlam hw h]
  rfl

/-- The family U on a layer without routed experts, whole: the value of the segment's form plus the
matrix products of the keys, written as a row of a panel would hold them. -/
theorem Fits.whole_U_even (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (lam : ℕ) (hlam : lam < D.nl) (hl : lam % 2 = 0) {ew wh : Array E}
    (hw : Wts ρ ew wh v.y.ls low D.f) {f : Aff} (h : v.line "U" lam ew wh = some f) :
    f.value ρ W + Inst.Model.Site.scl (D.Pl lam).ku
        (∑ j ∈ range D.d, valU D t .m lam j u * ∑ x ∈ range D.f, wt ρ ew x * (w lam).Wu j x) =
      ∑ x ∈ range (len D .U), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => key D t tb L0 w .U lam x i) u := by
  have e : ∀ x, x < D.f → ∀ i, key D t tb L0 w .U lam x i =
      lin D t tb L0 w .U lam x i + mat D t w .U lam x i := by
    intro x hx i
    have hr : routed D lam x = false := routed_false D (by rw [fSh_even D hl]; exact hx)
    rw [Inst.Model.FFSeg.key_eq]
    simp [term, hr]
  show _ = wsum (wt ρ ew) D.lT u D.f (fun x i => key D t tb L0 w .U lam x i)
  rw [wsum_congr _ _ _ _ e, wsum_add, acc_U_even D t w (wt ρ ew) u hl,
    F.line_U tb L0 w lam hlam hw h]
  rfl

end Whole

/-! ## What panelA appends -/

section PanelEqs

/-- What panelA appends for the segment O. -/
theorem panelA_O_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelA p ec el "O" s = Model.Layer.plain p.v.y ec 0 false p.v.y.dq
      (some fun lam k2 =>
        if p.v.y.h.p4 then p.v.shIn (p.v.tensorAt "o" "zt") lam k2
        else some (Model.Layer.stubAt p (Model.eqTab p.zt) lam k2)) none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lko))
      none s := rfl

/-- What panelA appends for the segment LR. -/
theorem panelA_LR_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelA p ec el "LR" s = Model.Layer.plain p.v.y ec 0 true p.v.y.h.d
      (some fun lam k2 => p.v.shIn (p.v.tensorAt "m" "zt") lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kTM p.v.sc (p.v.lay lam) 0))
      none s := rfl

/-- What panelA appends for the segment G. -/
theorem panelA_G_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelA p ec el "G" s = Model.Layer.plain p.v.y ec 0 false p.v.y.h.d
      (some fun lam k2 => p.v.shIn (p.v.tensorAt "m" "zt") lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lkg))
      none s := rfl

/-- What panelA appends for the segment U. -/
theorem panelA_U_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelA p ec el "U" s = Model.Layer.plain p.v.y ec 0 false p.v.y.h.d
      (some fun lam k2 => p.v.shIn (p.v.tensorAt "m" "zt") lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (Model.Layer.kT p.v.sc (p.v.lay lam) Model.Layer.Lku))
      none s := rfl

end PanelEqs

section PanelSpecs

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K}

/-- The panel that the verifier appends for the segment O at profile 4, against the library's panel
Pan.O: as many rows (Pan.nr) and columns (Pan.nc); the A side at (layer, channel) is worth Pan.A at
any record of reads whose o1 is the extension of the attention output o at the lookup's token point
(rdTrue has that o1); the weight of a row of the group is the layer's weight under the factor
2^max(0, 16 - ko), which is the shape of Pan.wt, with the layer's weight left free; the B side is a
weight matrix, with one weight claim for each row. h4: the profile is 4. ho: the array o is found,
tied and true at the token point. At profile 3 the A side is a public number, and this theorem says
nothing of it. -/
theorem panelO_spec (F : Fits ρ W v D c t low u) (h4 : v.y.h.p4 = true)
    (ho : HasShort ρ W v D c t u .o) (p : PanelEnv) (hp : p.v = v) (ec : E)
    (el : Array E) (s : Panels) :
    ∃ b : SBlk, (panelA p ec el "O" s).bl = s.bl.push b ∧
      (panelA p ec el "O" s).nextV = s.nextV + v.y.Lam ∧
      b.tri = false ∧ b.claim = 0 ∧ b.ec = ec ∧ b.ni = Pan.O.nr D ∧ b.ny = Pan.O.nc D ∧
      b.v0 = some s.nextV ∧ b.virt = none ∧ b.B.isNone = true ∧
      (∃ A, b.A = some A ∧ ∀ (r : Rd K), (∀ l j, r.o1 l j = valU D t .o l j u) →
        ∀ lam k2 a, A lam k2 = some a → a.value ρ W = Pan.O.A D r lam k2) ∧
      ∀ lam, lam < v.y.Lam → ρ.val (b.wt.getD lam zeroE) =
        Inst.Model.Site.scl (D.Pl lam).ko (ρ.val (el.getD lam zeroE)) := by
  subst hp
  rw [panelA_O_eq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, F.Lam, F.dq, rfl, rfl, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · intro r hr lam k2 a ha
    have ha' : (if p.v.y.h.p4 then p.v.shIn (p.v.tensorAt "o" "zt") lam k2 else _) = some a := ha
    rw [h4] at ha'
    have ha'' : p.v.shA "o" "zt" lam k2 = some a := ha'
    obtain ⟨ten, b, h1, T, R⟩ := ho
    show _ = r.o1 lam k2
    rw [shA_true F.num T R h1 ha'', hr, ext_raw D t u rfl]
  · intro lam hlam
    show ρ.val (((Array.range p.v.y.Lam).map fun i => mulE (el.getD i zeroE) (Model.Layer.pw
      (Model.Layer.tOf (p.v.sc.kl (p.v.lay i) Model.Layer.Lko)))).getD lam zeroE) = _
    rw [range_map_getD _ _ hlam, F.ko lam (F.Lam ▸ hlam), scl_weight F.num]

/-- The panel that the verifier appends for the segment LR, against the library's panel Pan.LR: as
many rows (Pan.nr: one for each layer with routed experts, row i for layer 2 i + 1 of the group) and
columns (Pan.nc); the A side at (row i, channel) is worth Pan.A at any record of reads whose m1 is
the extension of the array m at the lookup's token point (rdTrue has that m1); the weight of row i
is the weight of layer 2 i + 1 under the factor 2^max(0, 16 - kr), which is the shape of Pan.wt,
with the layer's weight left free; the B side is a weight matrix, with one weight claim for each
row. -/
theorem panelLR_spec (F : Fits ρ W v D c t low u) (p : PanelEnv) (hp : p.v = v) (ec : E)
    (el : Array E) (s : Panels) :
    ∃ b : SBlk, (panelA p ec el "LR" s).bl = s.bl.push b ∧
      (panelA p ec el "LR" s).nextV = s.nextV + v.y.LamM ∧
      b.tri = false ∧ b.claim = 0 ∧ b.ec = ec ∧ b.ni = Pan.LR.nr D ∧ b.ny = Pan.LR.nc D ∧
      b.v0 = some s.nextV ∧ b.virt = none ∧ b.B.isNone = true ∧
      (∃ A, b.A = some A ∧ ∀ (r : Rd K), (∀ l j, r.m1 l j = valU D t .m l j u) →
        ∀ i k2 a, A i k2 = some a → a.value ρ W = Pan.LR.A D r i k2) ∧
      ∀ i, i < v.y.LamM → ρ.val (b.wt.getD i zeroE) =
        Inst.Model.Site.scl (D.Pl (2 * i + 1)).kr (ρ.val (el.getD (2 * i + 1) zeroE)) := by
  subst hp
  rw [panelA_LR_eq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, F.LamM, F.d, rfl, rfl, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · intro r hr i k2 a ha
    have ha' : p.v.shA "m" "zt" (2 * i + 1) k2 = some a := ha
    show _ = r.m1 (2 * i + 1) k2
    rw [F.shA .m rfl ha', hr, ext_raw D t u rfl]
  · intro i hi
    show ρ.val (((Array.range p.v.y.LamM).map fun i => mulE (el.getD (2 * i + 1) zeroE)
      (Model.Layer.pw (Model.Layer.tOf (p.v.sc.klM (p.v.lay (2 * i + 1)) 0)))).getD i zeroE) = _
    have hne : i < D.nl / 2 := by
      have h1 := F.LamM
      unfold Inst.Model.FFSeg.Dim.ne at h1
      omega
    rw [range_map_getD _ _ hi, F.kr (2 * i + 1) (by omega) (by omega), scl_weight F.num]

/-- The panel that the verifier appends for the segment G, against the library's panel Pan.G: as
many rows (Pan.nr) and columns (Pan.nc); the A side at (layer, channel) is worth Pan.A at any record
of reads whose m1 is the extension of the array m at the lookup's token point (rdTrue has that m1);
the weight of a row of the group is the layer's weight under the factor 2^max(0, 16 - kg), which is
the shape of Pan.wt, with the layer's weight left free; the B side is a weight matrix, with one
weight claim for each row. -/
theorem panelG_spec (F : Fits ρ W v D c t low u) (p : PanelEnv) (hp : p.v = v) (ec : E)
    (el : Array E) (s : Panels) :
    ∃ b : SBlk, (panelA p ec el "G" s).bl = s.bl.push b ∧
      (panelA p ec el "G" s).nextV = s.nextV + v.y.Lam ∧
      b.tri = false ∧ b.claim = 0 ∧ b.ec = ec ∧ b.ni = Pan.G.nr D ∧ b.ny = Pan.G.nc D ∧
      b.v0 = some s.nextV ∧ b.virt = none ∧ b.B.isNone = true ∧
      (∃ A, b.A = some A ∧ ∀ (r : Rd K), (∀ l j, r.m1 l j = valU D t .m l j u) →
        ∀ lam k2 a, A lam k2 = some a → a.value ρ W = Pan.G.A D r lam k2) ∧
      ∀ lam, lam < v.y.Lam → ρ.val (b.wt.getD lam zeroE) =
        Inst.Model.Site.scl (D.Pl lam).kg (ρ.val (el.getD lam zeroE)) := by
  subst hp
  rw [panelA_G_eq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, F.Lam, F.d, rfl, rfl, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · intro r hr lam k2 a ha
    have ha' : p.v.shA "m" "zt" lam k2 = some a := ha
    show _ = r.m1 lam k2
    rw [F.shA .m rfl ha', hr, ext_raw D t u rfl]
  · intro lam hlam
    show ρ.val (((Array.range p.v.y.Lam).map fun i => mulE (el.getD i zeroE) (Model.Layer.pw
      (Model.Layer.tOf (p.v.sc.kl (p.v.lay i) Model.Layer.Lkg)))).getD lam zeroE) = _
    rw [range_map_getD _ _ hlam, F.kg lam (F.Lam ▸ hlam), scl_weight F.num]

/-- The panel that the verifier appends for the segment U, against the library's panel Pan.U: as
panelG_spec, with the shift ku. -/
theorem panelU_spec (F : Fits ρ W v D c t low u) (p : PanelEnv) (hp : p.v = v) (ec : E)
    (el : Array E) (s : Panels) :
    ∃ b : SBlk, (panelA p ec el "U" s).bl = s.bl.push b ∧
      (panelA p ec el "U" s).nextV = s.nextV + v.y.Lam ∧
      b.tri = false ∧ b.claim = 0 ∧ b.ec = ec ∧ b.ni = Pan.U.nr D ∧ b.ny = Pan.U.nc D ∧
      b.v0 = some s.nextV ∧ b.virt = none ∧ b.B.isNone = true ∧
      (∃ A, b.A = some A ∧ ∀ (r : Rd K), (∀ l j, r.m1 l j = valU D t .m l j u) →
        ∀ lam k2 a, A lam k2 = some a → a.value ρ W = Pan.U.A D r lam k2) ∧
      ∀ lam, lam < v.y.Lam → ρ.val (b.wt.getD lam zeroE) =
        Inst.Model.Site.scl (D.Pl lam).ku (ρ.val (el.getD lam zeroE)) := by
  subst hp
  rw [panelA_U_eq]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, F.Lam, F.d, rfl, rfl, rfl, ⟨_, rfl, ?_⟩, ?_⟩
  · intro r hr lam k2 a ha
    have ha' : p.v.shA "m" "zt" lam k2 = some a := ha
    show _ = r.m1 lam k2
    rw [F.shA .m rfl ha', hr, ext_raw D t u rfl]
  · intro lam hlam
    show ρ.val (((Array.range p.v.y.Lam).map fun i => mulE (el.getD i zeroE) (Model.Layer.pw
      (Model.Layer.tOf (p.v.sc.kl (p.v.lay i) Model.Layer.Lku)))).getD lam zeroE) = _
    rw [range_map_getD _ _ hlam, F.ku lam (F.Lam ▸ hlam), scl_weight F.num]

end PanelSpecs

#print axioms acc_O
#print axioms acc_LR
#print axioms acc_G
#print axioms acc_U
#print axioms acc_G_even
#print axioms acc_G_odd
#print axioms acc_U_even
#print axioms acc_U_odd
#print axioms acc_D
#print axioms Fits.whole_O
#print axioms Fits.whole_LR
#print axioms Fits.whole_G_even
#print axioms Fits.whole_U_even
#print axioms panelO_spec
#print axioms panelLR_spec
#print axioms panelG_spec
#print axioms panelU_spec

end OnBytes.Road
