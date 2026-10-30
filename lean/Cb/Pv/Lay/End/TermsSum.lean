-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/TermsSum.lean: the sum of the late panels' shares of a group of layers, term by term:
each term is a coefficient, at most one shown contraction, and one kept value.

The sumcheck of the terms of a layers' sub-proof has the summand Gpos (Inst/Model/FF/Objects.lean).
At a point, Gpos is the sum Sig1 of the shares of the late panels at the contractions of the cells
at that point. This file writes Sig1, at any record r of contractions, as a sum of terms of one
form:
  (a coefficient) * (a contraction that the sumcheck shows, or none) * (a kept value).
The shown contractions are R2, sc2 and sel2 of r. A kept value is a linear combination of
contractions of r that are never shown, under weights that may hold entries of the weight matrices.

Main names:
  `kQK`, `kXR`, `kG`, `kU`, `kD`: the kept values that are sums; the others are r.xF and r.lr2.
  `share_N1`, `share_N2`, `share_QK`, `share_XR`, `share_DD`, `share_MR`, `share_Gr`, `share_Ur`,
  `share_Dr`: the share of each late panel in that form.
  `late_pans`: the list of the late panels.
  `sig1_terms`: Sig1 as the sum of the nine kinds of terms.
Limits: in the terms of the panel QK the coefficient holds kp, which reads the rotary tables at the
point zh: it is public, but it is a function of the point, of degree 1 in each coordinate, and no
contraction is shown beside it. Identities in a field alone: nothing on a sumcheck, on a
distribution of a challenge or on soundness.


-/
import Inst.Model.FF.Objects

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim LW Pan Rd pans Sig1 wc call AH kp Wqk ew)

variable {E : Type} [Field E]

/-- A sum over a list of the first n numbers is the sum over the range. -/
theorem listRange_sum (g : ℕ → E) (n : ℕ) : ((List.range n).map g).sum = ∑ x ∈ range n, g x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- The late panels. -/
theorem late_pans (D : Dim) : (pans D).filter (fun p => p.late) =
    (List.range D.ne).map .Gr ++ (List.range D.ne).map .Ur ++ [.N1, .N2] ++
      (List.range D.ne).map .Dr ++ [.QK, .XR, .DD, .MR] := by
  have hm : ∀ f : ℕ → Pan, (∀ n, (f n).late = true) → ∀ l : List ℕ,
      (l.map f).filter (fun p => p.late) = l.map f := by
    intro f hf l
    rw [List.filter_eq_self]
    intro a ha
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp ha
    exact hf n
  unfold pans
  simp only [List.filter_append]
  rw [hm Pan.Gr (fun _ => rfl), hm Pan.Ur (fun _ => rfl), hm Pan.Dr (fun _ => rfl)]
  rfl

variable [scl : Scl] (D : Dim) (r : Rd E) (tb : Tables) (L0 : ℕ) (w : ℕ → LW E) (z zh : ℕ → E)

/-! ## The kept values -/

/-- Channel x of a head, layer l: the contractions of a under the weights of queries and keys,
summed over the heads under their weights. -/
def kQK (l x : ℕ) : E :=
  ∑ j ∈ range D.d, r.a2 l j * ∑ h ∈ range (D.P.nq + D.P.nkv), AH D z h * Wqk D w l j h x

/-- Routed layer l': the contractions of m under the weights of the family XR. -/
def kXR (l' : ℕ) : E := ∑ x ∈ range D.d, ew D z .XR x * r.m2 (2 * l' + 1) x

/-- Routed layer l', expert e: the contractions of xr under the gate's weights. -/
def kG (l' e : ℕ) : E := ∑ j ∈ range D.d, r.xr2 l' j * (Pan.Gr l').B D r tb L0 w z zh e j

/-- The same under the up product's weights. -/
def kU (l' e : ℕ) : E := ∑ j ∈ range D.d, r.xr2 l' j * (Pan.Ur l').B D r tb L0 w z zh e j

/-- Routed layer l', expert e: the entries of the routed gated products under the down product's
weights. -/
def kD (l' e : ℕ) : E := ∑ j ∈ range D.fe, r.hh2 l' j * (Pan.Dr l').B D r tb L0 w z zh e j

/-! ## The shares -/

omit scl in
/-- A panel with one column. -/
theorem share_col (c : E) (n : ℕ) (wt a b : ℕ → E) :
    c * ∑ ρ ∈ range n, wt ρ * ∑ _ι ∈ range 1, a ρ * b ρ = ∑ ρ ∈ range n, c * wt ρ * a ρ * b ρ := by
  rw [mul_sum]
  exact sum_congr rfl fun ρ _ => by rw [sum_range_one]; ring

theorem share_N1 : Pan.N1.share D r tb L0 w z zh =
    ∑ l ∈ range D.nl, wc D z (call .N1) * Pan.N1.wt D z l * r.R2 (2 * l) * r.xF (2 * l) :=
  share_col _ _ _ _ _

theorem share_N2 : Pan.N2.share D r tb L0 w z zh =
    ∑ l ∈ range D.nl,
      wc D z (call .N2) * Pan.N2.wt D z l * r.R2 (2 * l + 1) * r.xF (2 * l + 1) :=
  share_col _ _ _ _ _

theorem share_XR : Pan.XR.share D r tb L0 w z zh =
    ∑ l' ∈ range D.ne, wc D z (call .XR) * Pan.XR.wt D z l' * r.sc2 l' * kXR D r z l' :=
  share_col _ _ _ _ _

omit scl in
/-- A panel whose entries are products of two contractions. -/
theorem share_flat (c : E) (n m : ℕ) (wt : ℕ → E) (a b : ℕ → ℕ → E) :
    c * ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, a ρ ι * b ρ ι =
      ∑ ρ ∈ range n, ∑ ι ∈ range m, c * wt ρ * a ρ ι * b ρ ι := by
  rw [mul_sum]
  refine sum_congr rfl fun ρ _ => ?_
  rw [mul_sum, mul_sum]
  exact sum_congr rfl fun ι _ => by ring

theorem share_DD : Pan.DD.share D r tb L0 w z zh =
    ∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .DD) * Pan.DD.wt D z l' * r.sel2 l' e * r.lr2 l' e :=
  share_flat _ _ _ _ _ _

theorem share_MR : Pan.MR.share D r tb L0 w z zh =
    ∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .MR) * Pan.MR.wt D z l' * r.sel2 l' e * r.lr2 l' e :=
  share_flat _ _ _ _ _ _

omit scl in
/-- A panel with three factors: the first hangs on the row alone. -/
theorem share_three (c : E) (n m : ℕ) (wt s : ℕ → E) (x : ℕ → E) (b : ℕ → ℕ → E) :
    c * ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, s ρ * x ι * b ρ ι =
      ∑ ρ ∈ range n, c * wt ρ * s ρ * ∑ ι ∈ range m, x ι * b ρ ι := by
  rw [mul_sum]
  refine sum_congr rfl fun ρ _ => ?_
  rw [mul_sum, mul_sum, mul_sum]
  exact sum_congr rfl fun ι _ => by ring

theorem share_Gr (l' : ℕ) : (Pan.Gr l').share D r tb L0 w z zh =
    ∑ e ∈ range D.nx,
      wc D z (call .G) * (Pan.Gr l').wt D z e * r.sel2 l' e * kG D r tb L0 w z zh l' e :=
  share_three _ _ _ _ _ _ _

theorem share_Ur (l' : ℕ) : (Pan.Ur l').share D r tb L0 w z zh =
    ∑ e ∈ range D.nx,
      wc D z (call .U) * (Pan.Ur l').wt D z e * r.sel2 l' e * kU D r tb L0 w z zh l' e :=
  share_three _ _ _ _ _ _ _

theorem share_Dr (l' : ℕ) : (Pan.Dr l').share D r tb L0 w z zh =
    ∑ e ∈ range D.nx,
      wc D z (call .D) * (Pan.Dr l').wt D z e * r.sel2 l' e * kD D r tb L0 w z zh l' e :=
  share_three _ _ _ _ _ _ _

omit scl in
/-- The sums of the panel QK in another order: the channel of a head outermost. -/
theorem qk_swap (n nh nx : ℕ) (a : ℕ → E) (ah k : ℕ → E) (W : ℕ → ℕ → ℕ → E) :
    ∑ ι ∈ range n, a ι * ∑ h ∈ range nh, ∑ x ∈ range nx, ah h * k x * W ι h x =
      ∑ x ∈ range nx, k x * ∑ ι ∈ range n, a ι * ∑ h ∈ range nh, ah h * W ι h x := by
  have L : ∑ ι ∈ range n, a ι * ∑ h ∈ range nh, ∑ x ∈ range nx, ah h * k x * W ι h x =
      ∑ ι ∈ range n, ∑ h ∈ range nh, ∑ x ∈ range nx, a ι * (ah h * k x * W ι h x) := by
    simp only [mul_sum]
  have R : ∑ x ∈ range nx, k x * ∑ ι ∈ range n, a ι * ∑ h ∈ range nh, ah h * W ι h x =
      ∑ x ∈ range nx, ∑ ι ∈ range n, ∑ h ∈ range nh, k x * (a ι * (ah h * W ι h x)) := by
    simp only [mul_sum]
  rw [L, R]
  calc ∑ ι ∈ range n, ∑ h ∈ range nh, ∑ x ∈ range nx, a ι * (ah h * k x * W ι h x)
      = ∑ ι ∈ range n, ∑ x ∈ range nx, ∑ h ∈ range nh, a ι * (ah h * k x * W ι h x) :=
        sum_congr rfl fun ι _ => sum_comm
    _ = ∑ x ∈ range nx, ∑ ι ∈ range n, ∑ h ∈ range nh, a ι * (ah h * k x * W ι h x) := sum_comm
    _ = ∑ x ∈ range nx, ∑ ι ∈ range n, ∑ h ∈ range nh, k x * (a ι * (ah h * W ι h x)) :=
        sum_congr rfl fun x _ => sum_congr rfl fun ι _ => sum_congr rfl fun h _ => by ring

theorem share_QK : Pan.QK.share D r tb L0 w z zh =
    ∑ l ∈ range D.nl, ∑ x ∈ range D.P.ch,
      wc D z (call .QK) * Pan.QK.wt D z l * kp D tb L0 z zh l x * kQK D r w z l x := by
  show wc D z (call .QK) * ∑ l ∈ range D.nl, Pan.QK.wt D z l * ∑ j ∈ range D.d, r.a2 l j *
      ∑ h ∈ range (D.P.nq + D.P.nkv), ∑ x ∈ range D.P.ch,
        AH D z h * kp D tb L0 z zh l x * Wqk D w l j h x = _
  rw [mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [qk_swap, mul_sum, mul_sum]
  exact sum_congr rfl fun x _ => by
    unfold kQK
    ring

/-! ## All late panels -/

/-- Sig1, term by term. -/
theorem sig1_terms : Sig1 D r tb L0 w z zh =
    (∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .G) * (Pan.Gr l').wt D z e * r.sel2 l' e * kG D r tb L0 w z zh l' e) +
    (∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .U) * (Pan.Ur l').wt D z e * r.sel2 l' e * kU D r tb L0 w z zh l' e) +
    (∑ l ∈ range D.nl, wc D z (call .N1) * Pan.N1.wt D z l * r.R2 (2 * l) * r.xF (2 * l)) +
    (∑ l ∈ range D.nl,
      wc D z (call .N2) * Pan.N2.wt D z l * r.R2 (2 * l + 1) * r.xF (2 * l + 1)) +
    (∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .D) * (Pan.Dr l').wt D z e * r.sel2 l' e * kD D r tb L0 w z zh l' e) +
    (∑ l ∈ range D.nl, ∑ x ∈ range D.P.ch,
      wc D z (call .QK) * Pan.QK.wt D z l * kp D tb L0 z zh l x * kQK D r w z l x) +
    (∑ l' ∈ range D.ne, wc D z (call .XR) * Pan.XR.wt D z l' * r.sc2 l' * kXR D r z l') +
    (∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .DD) * Pan.DD.wt D z l' * r.sel2 l' e * r.lr2 l' e) +
    (∑ l' ∈ range D.ne, ∑ e ∈ range D.nx,
      wc D z (call .MR) * Pan.MR.wt D z l' * r.sel2 l' e * r.lr2 l' e) := by
  unfold Sig1
  rw [late_pans]
  simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Function.comp_def, listRange_sum]
  rw [share_N1, share_N2, share_QK, share_XR, share_DD, share_MR]
  simp only [share_Gr, share_Ur, share_Dr]
  ring

end Cb.Pv.Lay.End

#print axioms Cb.Pv.Lay.End.sig1_terms
