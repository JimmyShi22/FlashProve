-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysXR.lean: the form of the segment XR plus the products of two cells in its
keys.

The key of the family XR holds the product of the score sc and the array m at one position. A sum of
such products over the positions, under the equality weights of the lookup's token point, is no form
in the reads. The verifier leaves it to a sumcheck over the positions (the second token sumcheck),
whose summand is a product of two multilinear extensions, and takes that summand's value at the
sumcheck's end point from a panel of the batched sumcheck.

This file has the identities around that step for XR:
 - the summand (hatXR: the library's termHat with the weights left free),
 - on the vertices of the cube the summand is the weighted sum of the products in the keys, so the
   sum that the sumcheck is to show is the missing part of the keys (term_XR, Fits.whole_XR),
 - what the verifier appends as the panel of XR (panelT_XR_eq), and what the B side of a row of it
   is worth on reads that are true at a point u' (rowXR_value); with the extension of the score for
   the A side the product of the two is the summand at u' (rowXR_hat).

What is not claimed: see Johnson/Road/FormsKeysKit.lean. That the sumcheck shows its sum, and how
the panel's rows are gathered, is not touched. The A side of the verifier's panel is the value that
was sent for sc. The verifier's claim on sc is on the hidden value under the same slot, which is the
sent one less a factor times a mask entry: in a run that hides, the sent value is not the extension
of sc. How the sumcheck's masks are accounted for is not looked at. The program does not import this
file.
-/
import Johnson.Road.FormsKeysB
import OnBytes.Model.LayerPanels

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env Ten)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin term mat len valU)

variable {K : Type} [Field K]

/-- The summand of the sumcheck over the positions for the family XR at layer l, under weights g:
the extension of the score times the weighted sum of the extensions of m. -/
def hatXR (D : Dim) (t : Cell → K) (g : ℕ → K) (l : ℕ) (X : ℕ → K) : K :=
  valU D t .sc (l / 2) 0 X * ∑ x ∈ range D.d, g x * valU D t .m l x X

/-- It is the library's summand, with the library's weights. -/
theorem hatXR_lib [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (z : ℕ → K) (l : ℕ) (X : ℕ → K) :
    Inst.Model.FFSeg.termHat D t tb L0 w z .XR l X =
      hatXR D t (fun x => Inst.Model.FFSeg.ew D z .XR x) l X := rfl

/-- The products in the keys of the family XR, summed under the weights g and the equality weights
of u, are the sum over the cube's vertices of the summand under the equality weights of u. -/
theorem term_XR [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (g : ℕ → K) (u : ℕ → K) (l : ℕ) :
    wsum g D.lT u D.d (fun x i => term D t tb L0 w .XR l x i) =
      Blocks.ext D.lT (fun i => hatXR D t g l (Blocks.cubePt D.lT i)) u := by
  have e : Blocks.ext D.lT (fun i => hatXR D t g l (Blocks.cubePt D.lT i)) u =
      Blocks.ext D.lT (fun i => ∑ x ∈ range D.d, g x *
        (Inst.Model.FFSeg.val t .sc (l / 2) 0 i * Inst.Model.FFSeg.val t .m l x i)) u := by
    refine Blocks.ext_congr (fun i hi => ?_) u
    unfold hatXR valU
    rw [Blocks.ext_cubePt _ _ hi, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [Blocks.ext_cubePt _ _ hi]
    ring
  rw [e, Blocks.ext_sum]
  unfold wsum
  refine sum_congr rfl fun x _ => ?_
  rw [Blocks.ext_smul]
  rfl

section Whole

variable [scl : Scl] {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K}

/-- The family XR, whole: the value of the segment's form plus the sum that the sumcheck over the
positions is to show for this family and layer is the weighted sum of the extensions of the
library's keys. -/
theorem Fits.whole_XR (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (lam : ℕ)
    {ew wh : Array E} (hsz : ew.size = len D .XR) {f : Aff} (h : v.line "XR" lam ew wh = some f) :
    f.value ρ W + Blocks.ext D.lT (fun i => hatXR D t (wt ρ ew) lam (Blocks.cubePt D.lT i)) u =
      ∑ x ∈ range (len D .XR), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => key D t tb L0 w .XR lam x i) u := by
  have e : ∀ x, x < D.d → ∀ i, key D t tb L0 w .XR lam x i =
      lin D t tb L0 w .XR lam x i + term D t tb L0 w .XR lam x i := by
    intro x _ i
    rw [Inst.Model.FFSeg.key_eq]
    simp [mat]
  show _ = wsum (wt ρ ew) D.lT u D.d (fun x i => key D t tb L0 w .XR lam x i)
  rw [wsum_congr _ _ _ _ e, wsum_add, term_XR, F.line_XR tb L0 w lam hsz h]
  rfl

omit [Field K] scl in
/-- What the verifier appends as the panel of the segment XR, with routed experts: one column; the
A side of a row is the value that was shown for the layer's score; the B side is the weighted sum of
the entries of m, read at the point named rt. -/
theorem panelT_XR_eq (p : Model.Layer.PanelEnv) (ec : E) (el : Array E) (s : Model.Layer.Panels) :
    Model.Layer.panelT p ec el "XR" s =
      (if !p.v.y.h.p3 then pure s
      else do
        let ew ← p.v.ewOf "XR"
        pure (Model.Layer.plain p.v.y ec 1 true 1
          (some fun lam _ =>
            some (Aff.ofConst (p.shownT.getD (p.v.y.NN * p.v.y.Lam + lam / 2) zeroE)))
          (some fun lam _ => p.v.shSum ew p.v.y.h.d "m" "rt" lam)
          (fun lam => el.getD lam zeroE) none s)) := by
  rfl

omit scl in
/-- The B side of the row of that panel for layer lam: if the short tables of m at the point named
rt are true at u', it is worth the weighted sum of the extensions of m at u'. -/
theorem rowXR_value (hρ : Numerals ρ) {u' : ℕ → K} {ten : Ten} {b : ℕ}
    (hX : v.tensorAt "m" "rt" = some (ten, b)) (T : Tied c t .m ten.mat ten.place)
    (R : ShortTrue ρ W v b ten.mat D.lT c u') (hd : v.y.h.d = D.d) (lam : ℕ) {ew : Array E}
    {B : Aff} (hB : v.shSum ew v.y.h.d "m" "rt" lam = some B) :
    B.value ρ W = ∑ x ∈ range D.d, wt ρ ew x * valU D t .m lam x u' := by
  rw [shSum_true hρ T R hX hB, hd]
  unfold wsum valU
  refine sum_congr rfl fun x _ => ?_
  congr 2
  funext i
  simp [raw, Arr.off]

omit scl in
/-- With the extension of the score at u' for the A side, the product of the row's two sides is the
summand at u'. The A side of the verifier's own panel is not that extension: it is the value that
was sent for the score; the verifier's claim that ties the score to its extension is on the hidden
value under the slot. -/
theorem rowXR_hat (hρ : Numerals ρ) {u' : ℕ → K} {ten : Ten} {b : ℕ}
    (hX : v.tensorAt "m" "rt" = some (ten, b)) (T : Tied c t .m ten.mat ten.place)
    (R : ShortTrue ρ W v b ten.mat D.lT c u') (hd : v.y.h.d = D.d) (lam : ℕ) {ew : Array E}
    {B : Aff} (hB : v.shSum ew v.y.h.d "m" "rt" lam = some B) :
    valU D t .sc (lam / 2) 0 u' * B.value ρ W = hatXR D t (wt ρ ew) lam u' := by
  rw [rowXR_value hρ hX T R hd lam hB]
  rfl

end Whole

#print axioms Fits.whole_XR
#print axioms rowXR_value
#print axioms rowXR_hat

end OnBytes.Road
