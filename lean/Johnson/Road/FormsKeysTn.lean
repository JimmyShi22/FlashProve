-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTn.lean: the library's panels on the library's layout of the weights.

Two texts of the library speak of weights under factors. Inst/Model/FF/Objects.lean defines, for
the panels of a feed-forward segment's batched sumcheck, the value of the tensor claim of a panel's
row (Pan.TnRow) or, for a panel with three factors, of the panel (Pan.TnPan): a sum of the B side
of the panel under equality weights, where the B side reads the weights w l of the segment's layers
as matrices. Inst/Model/Common/TensorClaim.lean defines a tensor claim on the committed matrix W
(TClaim): the number of a unit of the layout of Inst/Model/Layout.lean, the unit, one factor for
each of its coordinates; and the claim's functional (TClaim.Tn): the sum over the unit's index
tuples of the product of the factors times the weight that the layout reads in W at that tuple.
This file joins the two, for the weights that the layout itself reads in W: w l := layerR D.P k W
(L0 + l) (Inst/Model/FF/Trace.lean).

Everything here compares objects of the library with objects of the library. One definition stands
between them, tnOf: which claim belongs to which panel and row. No theorem names the verifier in
OnBytes/. The weight that the layout reads at an index tuple stands twice in the library, with one
body: entryR (Inst/Model/FF/Trace.lean), which layerR reads, and entryW
(Inst/Model/Common/TensorClaim.lean), which TClaim.Tn reads. The theorems here pass one for the
other by unfolding the two definitions.

Main definitions: tnOf; layerOfRow. Main theorems.
 - TnRow_Tn: for the seven weight panels with two factors (G, U, V, O, D, LR, QK) and every row
   number ρ: p.TnRow at these weights is (tnOf p ρ).Tn D.P k W. One theorem for each panel stands
   before it, with the hypotheses that the panel needs and no other.
 - TnPan_Tn: the same for Gr l', Ur l', Dr l' and TnPan.
 - tnOf_unit: the claim's unit is the unit that the library's list of units has under the claim's
   number, if the row's layer is a layer of the model.
 - Wg_eq, Wu_eq, Wd_eq, Wr_eq, Eg_eq, Eu_eq, Ed_eq, Wqk_eq: what layerR reads, matrix by matrix.

The cuts. G, U: the panel sums over the fSh l hidden units that are not routed, and the layer's
unit has as many. D: the panel has f columns, its B side is 0 from fSh l on, and the unit has fSh l
rows. QK: the unit's first coordinate has 64 places, the panel sums over nq + nkv heads; the
claim's first factor is the library's AH on the heads and 0 above.

The hypotheses, and that they can be met.
 - L0 % 2 = 0 (G, U, D, LR, Gr, Ur, Dr): the model's layers with experts are the odd ones, the
   segment's too. Met by L0 = 0.
 - D.fe ≤ D.f (D alone). Met by the reference sizes (ref_fe) and by all sizes with the library's
   Dim.OK (fe_of_ok).
 - D.P.nq + D.P.nkv ≤ 64 (QK alone). Met by the reference sizes (ref_heads).
 - L0 + the row's layer < D.P.layers (tnOf_unit alone). The two main theorems do not ask it, nor a
   bound on the row's number: layerR and TClaim.Tn read W by the layout's formulas at any number.
   No hypothesis on k or W.

What is not claimed. Nothing is said of the panels without weights, of the A sides, of the
embedding and the output matrix, or of the form in which the library's merge takes a claim
(Inst/Model/LayoutSplit.lean: that the factors are products over the split). The program does
not import this file.
-/
import Inst.Model.FF.Objects
import Inst.Model.FF.IndexFacts
import Inst.Model.Common.TensorClaim

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Tables TClaim entryW hasExperts)
open Inst.Model.Layout (first uQK uV uO uGU uD uGUr uDr uR units layerUnits)
open Inst.Model.FFSeg (Dim Pan Rd LW layerR entryR matR isExpL fSh ew AH kp Wqk)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A sum over the rows and columns of a matrix that is cut to r rows and c columns, under one
factor for the row and one for the column. -/
theorem sum_matR (r c : ℕ) (f g : ℕ → K) (F : ℕ → ℕ → K) :
    ∑ i ∈ range r, f i * ∑ x ∈ range c, g x * matR r c F i x =
      ∑ i ∈ range r, ∑ x ∈ range c, f i * g x * F i x := by
  refine sum_congr rfl fun i hi => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x hx => ?_
  unfold matR
  rw [if_pos ⟨mem_range.mp hi, mem_range.mp hx⟩]
  ring

/-- A sum whose terms vanish from m on stops at m. -/
theorem sum_cut {m n : ℕ} (h : m ≤ n) (f g : ℕ → K) :
    ∑ i ∈ range n, f i * (if i < m then g i else 0) = ∑ i ∈ range m, f i * g i := by
  rw [← sum_subset (range_subset_range.mpr h)]
  · exact sum_congr rfl fun i hi => by rw [if_pos (mem_range.mp hi)]
  · intro i _ hi
    rw [if_neg (fun hc => hi (mem_range.mpr hc)), mul_zero]

/-- From an even layer on, the layers with experts are those that the segment counts as such. -/
theorem experts_iff {L0 : ℕ} (h0 : L0 % 2 = 0) (l : ℕ) :
    hasExperts (L0 + l) ↔ isExpL l = true := by
  unfold hasExperts isExpL
  rw [beq_iff_eq]
  omega

/-! ## The weights that layerR reads, matrix by matrix -/

section Weights

variable (D : Dim) (k : ℕ) (W : ℕ → ℕ → K) {L0 : ℕ} (h0 : L0 % 2 = 0)

include h0 in
/-- The gate's matrix of layer L0 + l that is not routed: d rows, fSh l columns, unit number 3 of
the layer. -/
theorem Wg_eq (l : ℕ) : (layerR D.P k W (L0 + l)).Wg =
    matR D.P.d (fSh D l) fun j x =>
      entryR D.P k W (first D.P (L0 + l) + 3) (uGU D.P (fSh D l)) [j, x] := by
  by_cases he : isExpL l = true
  · have hf : fSh D l = D.P.fe := if_pos he
    rw [hf]
    show (if hasExperts (L0 + l) then _ else _) = _
    rw [if_pos ((experts_iff h0 l).mpr he)]
  · have hf : fSh D l = D.P.f := if_neg he
    rw [hf]
    show (if hasExperts (L0 + l) then _ else _) = _
    rw [if_neg fun hc => he ((experts_iff h0 l).mp hc)]

include h0 in
/-- The same for the up projection: unit number 4 of the layer. -/
theorem Wu_eq (l : ℕ) : (layerR D.P k W (L0 + l)).Wu =
    matR D.P.d (fSh D l) fun j x =>
      entryR D.P k W (first D.P (L0 + l) + 4) (uGU D.P (fSh D l)) [j, x] := by
  by_cases he : isExpL l = true
  · have hf : fSh D l = D.P.fe := if_pos he
    rw [hf]
    show (if hasExperts (L0 + l) then _ else _) = _
    rw [if_pos ((experts_iff h0 l).mpr he)]
  · have hf : fSh D l = D.P.f := if_neg he
    rw [hf]
    show (if hasExperts (L0 + l) then _ else _) = _
    rw [if_neg fun hc => he ((experts_iff h0 l).mp hc)]

include h0 in
/-- The down projection that is not routed: fSh l rows, d columns; unit number 7 of a layer with
experts, 5 of a dense one. -/
theorem Wd_eq (l : ℕ) : (layerR D.P k W (L0 + l)).Wd =
    matR (fSh D l) D.P.d fun j x =>
      entryR D.P k W (first D.P (L0 + l) + if isExpL l then 7 else 5) (uD D.P (fSh D l))
        [j, x] := by
  by_cases he : isExpL l = true
  · have hf : fSh D l = D.P.fe := if_pos he
    rw [hf, if_pos he]
    show (if hasExperts (L0 + l) then _ else _) = _
    rw [if_pos ((experts_iff h0 l).mpr he)]
  · have hf : fSh D l = D.P.f := if_neg he
    rw [hf, if_neg he]
    show (if hasExperts (L0 + l) then _ else _) = _
    rw [if_neg fun hc => he ((experts_iff h0 l).mp hc)]

/-- The router's matrix of a layer with experts: unit number 9. -/
theorem Wr_eq {L : ℕ} (hx : hasExperts L) : (layerR D.P k W L).Wr =
    matR D.P.d D.P.nexp fun j e => entryR D.P k W (first D.P L + 9) (uR D.P) [j, e] := by
  show (if hasExperts L then _ else _) = _
  rw [if_pos hx]

/-- The gate's matrix of routed expert e: unit number 5, with e for the second coordinate. -/
theorem Eg_eq {L e : ℕ} (hx : hasExperts L) (he : e < D.P.nexp) : (layerR D.P k W L).Eg e =
    matR D.P.d D.P.fe fun j x => entryR D.P k W (first D.P L + 5) (uGUr D.P) [j, e, x] := by
  show (if hasExperts L ∧ e < D.P.nexp then _ else _) = _
  rw [if_pos ⟨hx, he⟩]

/-- The same for the up projection: unit number 6. -/
theorem Eu_eq {L e : ℕ} (hx : hasExperts L) (he : e < D.P.nexp) : (layerR D.P k W L).Eu e =
    matR D.P.d D.P.fe fun j x => entryR D.P k W (first D.P L + 6) (uGUr D.P) [j, e, x] := by
  show (if hasExperts L ∧ e < D.P.nexp then _ else _) = _
  rw [if_pos ⟨hx, he⟩]

/-- The down projection of routed expert e: unit number 8. -/
theorem Ed_eq {L e : ℕ} (hx : hasExperts L) (he : e < D.P.nexp) : (layerR D.P k W L).Ed e =
    matR D.P.fe D.P.d fun j x => entryR D.P k W (first D.P L + 8) (uDr D.P) [j, e, x] := by
  show (if hasExperts L ∧ e < D.P.nexp then _ else _) = _
  rw [if_pos ⟨hx, he⟩]

/-- Queries and keys, head by head: for a head h below nq + nkv, a channel x of a head and an input
j, the library's Wqk is the entry (h, x, j) of the layer's first unit. -/
theorem Wqk_eq (L0 l : ℕ) {j h x : ℕ} (hj : j < D.P.d) (hh : h < D.P.nq + D.P.nkv)
    (hx : x < D.P.ch) :
    Wqk D (fun l => layerR D.P k W (L0 + l)) l j h x =
      entryR D.P k W (first D.P (L0 + l)) (uQK D.P) [h, x, j] := by
  have hch : 0 < D.P.ch := Nat.lt_of_le_of_lt (Nat.zero_le _) hx
  have e1 : ∀ a, (D.P.ch * a + x) / D.P.ch = a := fun a => by
    rw [Nat.mul_add_div hch, Nat.div_eq_of_lt hx, Nat.add_zero]
  have e2 : ∀ a, (D.P.ch * a + x) % D.P.ch = x := fun a => by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hx]
  have e3 : ∀ a m, a < m → D.P.ch * a + x < m * D.P.ch := fun a m ha => by
    rw [Nat.mul_comm D.P.ch a]
    exact Inst.Model.FFSeg.IndexFacts.mr_lt ha hx
  unfold Wqk
  by_cases hq : h < D.P.nq
  · rw [if_pos hq]
    show (if j < D.P.d ∧ D.P.ch * h + x < D.P.nq * D.P.ch then
      entryR D.P k W (first D.P (L0 + l)) (uQK D.P)
        [(D.P.ch * h + x) / D.P.ch, (D.P.ch * h + x) % D.P.ch, j] else 0) = _
    rw [if_pos ⟨hj, e3 h _ hq⟩, e1, e2]
  · rw [if_neg hq]
    have hk : h - D.P.nq < D.P.nkv := by omega
    have eh : D.P.nq + (h - D.P.nq) = h := by omega
    show (if j < D.P.d ∧ D.P.ch * (h - D.P.nq) + x < D.P.nkv * D.P.ch then
      entryR D.P k W (first D.P (L0 + l)) (uQK D.P)
        [D.P.nq + (D.P.ch * (h - D.P.nq) + x) / D.P.ch, (D.P.ch * (h - D.P.nq) + x) % D.P.ch, j]
      else 0) = _
    rw [if_pos ⟨hj, e3 _ _ hk⟩, e1, e2, eh]

end Weights

/-! ## The claims -/

section Claims

variable (D : Dim) (tb : Tables) (L0 : ℕ) (z zh ζ : ℕ → K)

/-- The tensor claim of row ρ of a weight panel (for a panel with three factors: of the panel): the
number of the unit in the library's order of the units, the unit, and one factor for each of its
coordinates. Ec and Er are the equality weights of the panel's columns and rows at ζ; ew those of a
family's entries at the lookup's point. In the panel QK the first coordinate has 64 places for
nq + nkv heads: the factor is AH on the heads and 0 above. A panel without weights has the empty
claim. -/
def tnOf : Pan → ℕ → TClaim K
  | .G, l => ⟨first D.P (L0 + l) + 3, uGU D.P (fSh D l), [Pan.G.Ec D ζ, ew D z .G]⟩
  | .U, l => ⟨first D.P (L0 + l) + 4, uGU D.P (fSh D l), [Pan.U.Ec D ζ, ew D z .U]⟩
  | .V, l => ⟨first D.P (L0 + l) + 1, uV D.P, [Pan.V.Ec D ζ, ew D z .V]⟩
  | .O, l => ⟨first D.P (L0 + l) + 2, uO D.P, [Pan.O.Ec D ζ, ew D z .O]⟩
  | .D, l => ⟨first D.P (L0 + l) + if isExpL l then 7 else 5, uD D.P (fSh D l),
      [Pan.D.Ec D ζ, ew D z .D]⟩
  | .LR, l' => ⟨first D.P (L0 + (2 * l' + 1)) + 9, uR D.P, [Pan.LR.Ec D ζ, ew D z .LR]⟩
  | .QK, l => ⟨first D.P (L0 + l), uQK D.P,
      [fun h => if h < D.P.nq + D.P.nkv then AH D z h else 0, kp D tb L0 z zh l, Pan.QK.Ec D ζ]⟩
  | .Gr l', _ => ⟨first D.P (L0 + (2 * l' + 1)) + 5, uGUr D.P,
      [(Pan.Gr l').Ec D ζ, (Pan.Gr l').Er D ζ, fun x => ew D z .G (D.fe + x)]⟩
  | .Ur l', _ => ⟨first D.P (L0 + (2 * l' + 1)) + 6, uGUr D.P,
      [(Pan.Ur l').Ec D ζ, (Pan.Ur l').Er D ζ, fun x => ew D z .U (D.fe + x)]⟩
  | .Dr l', _ => ⟨first D.P (L0 + (2 * l' + 1)) + 8, uDr D.P,
      [(Pan.Dr l').Ec D ζ, (Pan.Dr l').Er D ζ, ew D z .D]⟩
  | _, _ => ⟨0, ⟨[], 0⟩, []⟩

end Claims

/-! ## The panels with two factors -/

section Two

variable (D : Dim) (r : Rd K) (tb : Tables) {L0 : ℕ} (h0 : L0 % 2 = 0) (k : ℕ) (W : ℕ → ℕ → K)
  (z zh ζ : ℕ → K)

/-- Panel V. -/
theorem TnRow_V (L0 l : ℕ) :
    Pan.V.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l =
      (tnOf D tb L0 z zh ζ .V l).Tn D.P k W := by
  show _ = (⟨_, uV D.P, [_, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_two D.P k W _ (uV D.P) _ _ rfl]
  exact sum_matR D.P.d (D.P.nkv * D.P.ch) _ _ _

/-- Panel O. -/
theorem TnRow_O (L0 l : ℕ) :
    Pan.O.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l =
      (tnOf D tb L0 z zh ζ .O l).Tn D.P k W := by
  show _ = (⟨_, uO D.P, [_, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_two D.P k W _ (uO D.P) _ _ rfl]
  exact sum_matR (D.P.nq * D.P.ch) D.P.d _ _ _

include h0 in
/-- Panel G: the columns of the gate that are not routed. -/
theorem TnRow_G (l : ℕ) :
    Pan.G.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l =
      (tnOf D tb L0 z zh ζ .G l).Tn D.P k W := by
  show ∑ i ∈ range D.P.d, Pan.G.Ec D ζ i *
      ∑ x ∈ range (fSh D l), ew D z .G x * (layerR D.P k W (L0 + l)).Wg i x =
    (⟨_, uGU D.P (fSh D l), [_, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_two D.P k W _ (uGU D.P (fSh D l)) _ _ rfl, Wg_eq D k W h0 l]
  exact sum_matR D.P.d (fSh D l) _ _ _

include h0 in
/-- Panel U. -/
theorem TnRow_U (l : ℕ) :
    Pan.U.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l =
      (tnOf D tb L0 z zh ζ .U l).Tn D.P k W := by
  show ∑ i ∈ range D.P.d, Pan.U.Ec D ζ i *
      ∑ x ∈ range (fSh D l), ew D z .U x * (layerR D.P k W (L0 + l)).Wu i x =
    (⟨_, uGU D.P (fSh D l), [_, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_two D.P k W _ (uGU D.P (fSh D l)) _ _ rfl, Wu_eq D k W h0 l]
  exact sum_matR D.P.d (fSh D l) _ _ _

include h0 in
/-- Panel D. The panel has f columns; from fSh l on its B side is 0, and the unit has fSh l rows. -/
theorem TnRow_D (hfe : D.fe ≤ D.f) (l : ℕ) :
    Pan.D.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l =
      (tnOf D tb L0 z zh ζ .D l).Tn D.P k W := by
  have hle : fSh D l ≤ D.f := by
    unfold fSh
    split_ifs
    · exact hfe
    · exact Nat.le_refl _
  show ∑ i ∈ range D.f, Pan.D.Ec D ζ i *
      (if i < fSh D l then ∑ x ∈ range D.P.d, ew D z .D x * (layerR D.P k W (L0 + l)).Wd i x
        else 0) =
    (⟨_, uD D.P (fSh D l), [_, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_two D.P k W _ (uD D.P (fSh D l)) _ _ rfl, sum_cut hle, Wd_eq D k W h0 l]
  exact sum_matR (fSh D l) D.P.d _ _ _

include h0 in
/-- Panel LR: row l' is the router of layer 2 l' + 1. -/
theorem TnRow_LR (l' : ℕ) :
    Pan.LR.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l' =
      (tnOf D tb L0 z zh ζ .LR l').Tn D.P k W := by
  have hx : hasExperts (L0 + (2 * l' + 1)) := by
    unfold hasExperts
    omega
  show ∑ i ∈ range D.P.d, Pan.LR.Ec D ζ i *
      ∑ x ∈ range D.P.nexp, ew D z .LR x * (layerR D.P k W (L0 + (2 * l' + 1))).Wr i x =
    (⟨_, uR D.P, [_, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_two D.P k W _ (uR D.P) _ _ rfl, Wr_eq D k W hx]
  exact sum_matR D.P.d D.P.nexp _ _ _

end Two

/-! ## The panel of queries and keys -/

section QK

variable (D : Dim) (r : Rd K) (tb : Tables) (L0 : ℕ) (k : ℕ) (W : ℕ → ℕ → K) (z zh ζ : ℕ → K)

/-- Panel QK. The unit's first coordinate has 64 places; the panel sums over the nq + nkv heads. So
at most 64 heads are asked, and the claim's first factor is 0 above the heads. -/
theorem TnRow_QK (hh : D.P.nq + D.P.nkv ≤ 64) (l : ℕ) :
    Pan.QK.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ l =
      (tnOf D tb L0 z zh ζ .QK l).Tn D.P k W := by
  show ∑ i ∈ range D.P.d, Pan.QK.Ec D ζ i *
      ∑ h ∈ range (D.P.nq + D.P.nkv), ∑ x ∈ range D.P.ch,
        AH D z h * kp D tb L0 z zh l x * Wqk D (fun l => layerR D.P k W (L0 + l)) l i h x =
    (⟨_, uQK D.P, [_, _, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_three D.P k W _ (uQK D.P) _ _ _ rfl]
  show _ = ∑ h ∈ range 64, ∑ x ∈ range D.P.ch, ∑ j ∈ range D.P.d,
    (if h < D.P.nq + D.P.nkv then AH D z h else 0) * kp D tb L0 z zh l x * Pan.QK.Ec D ζ j *
      entryW D.P k W (first D.P (L0 + l)) (uQK D.P) [h, x, j]
  have s1 : ∀ i ∈ range D.P.d, Pan.QK.Ec D ζ i *
      ∑ h ∈ range (D.P.nq + D.P.nkv), ∑ x ∈ range D.P.ch,
        AH D z h * kp D tb L0 z zh l x * Wqk D (fun l => layerR D.P k W (L0 + l)) l i h x =
      ∑ h ∈ range (D.P.nq + D.P.nkv), ∑ x ∈ range D.P.ch,
        AH D z h * kp D tb L0 z zh l x * Pan.QK.Ec D ζ i *
          entryW D.P k W (first D.P (L0 + l)) (uQK D.P) [h, x, i] := by
    intro i hi
    rw [mul_sum]
    refine sum_congr rfl fun h hh' => ?_
    rw [mul_sum]
    refine sum_congr rfl fun x hx => ?_
    rw [Wqk_eq D k W L0 l (mem_range.mp hi) (mem_range.mp hh') (mem_range.mp hx)]
    show _ * (_ * entryW D.P k W (first D.P (L0 + l)) (uQK D.P) [h, x, i]) = _
    ring
  rw [sum_congr rfl s1, sum_comm, ← sum_subset (range_subset_range.mpr hh)]
  · refine sum_congr rfl fun h hh' => ?_
    rw [sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun j _ => ?_
    rw [if_pos (mem_range.mp hh')]
  · intro h _ hn
    refine sum_eq_zero fun x _ => sum_eq_zero fun j _ => ?_
    rw [if_neg fun hc => hn (mem_range.mpr hc)]
    ring

end QK

/-! ## The panels with three factors -/

section Three

variable (D : Dim) (r : Rd K) (tb : Tables) {L0 : ℕ} (h0 : L0 % 2 = 0) (k : ℕ) (W : ℕ → ℕ → K)
  (z zh ζ : ℕ → K)

/-- A sum over experts, rows and columns, under one factor for each, with the expert's number in the
middle of the index tuple. -/
theorem sum_three (n r' c : ℕ) (fe' fr fc : ℕ → K) (M : ℕ → ℕ → ℕ → K) (F : ℕ → ℕ → ℕ → K)
    (hM : ∀ e, e < n → M e = matR r' c fun j x => F j e x) :
    ∑ e ∈ range n, fe' e * ∑ i ∈ range r', fr i * ∑ x ∈ range c, fc x * M e i x =
      ∑ i ∈ range r', ∑ e ∈ range n, ∑ x ∈ range c, fr i * fe' e * fc x * F i e x := by
  have s1 : ∀ e ∈ range n, fe' e * ∑ i ∈ range r', fr i * ∑ x ∈ range c, fc x * M e i x =
      ∑ i ∈ range r', ∑ x ∈ range c, fr i * fe' e * fc x * F i e x := by
    intro e he
    rw [hM e (mem_range.mp he), sum_matR, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun x _ => by ring
  rw [sum_congr rfl s1, sum_comm]

include h0 in
/-- Panel Gr l': the routed experts' gates of layer 2 l' + 1. -/
theorem TnPan_Gr (l' : ℕ) :
    (Pan.Gr l').TnPan D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ =
      (tnOf D tb L0 z zh ζ (.Gr l') 0).Tn D.P k W := by
  have hx : hasExperts (L0 + (2 * l' + 1)) := by
    unfold hasExperts
    omega
  show ∑ e ∈ range D.P.nexp, (Pan.Gr l').Er D ζ e * ∑ i ∈ range D.P.d, (Pan.Gr l').Ec D ζ i *
      ∑ x ∈ range D.P.fe, ew D z .G (D.fe + x) * (layerR D.P k W (L0 + (2 * l' + 1))).Eg e i x =
    (⟨_, uGUr D.P, [_, _, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_three D.P k W _ (uGUr D.P) _ _ _ rfl]
  exact sum_three D.P.nexp D.P.d D.P.fe _ _ _ _
    (fun j e x => entryR D.P k W (first D.P (L0 + (2 * l' + 1)) + 5) (uGUr D.P) [j, e, x])
    fun e he => Eg_eq D k W hx he

include h0 in
/-- Panel Ur l'. -/
theorem TnPan_Ur (l' : ℕ) :
    (Pan.Ur l').TnPan D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ =
      (tnOf D tb L0 z zh ζ (.Ur l') 0).Tn D.P k W := by
  have hx : hasExperts (L0 + (2 * l' + 1)) := by
    unfold hasExperts
    omega
  show ∑ e ∈ range D.P.nexp, (Pan.Ur l').Er D ζ e * ∑ i ∈ range D.P.d, (Pan.Ur l').Ec D ζ i *
      ∑ x ∈ range D.P.fe, ew D z .U (D.fe + x) * (layerR D.P k W (L0 + (2 * l' + 1))).Eu e i x =
    (⟨_, uGUr D.P, [_, _, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_three D.P k W _ (uGUr D.P) _ _ _ rfl]
  exact sum_three D.P.nexp D.P.d D.P.fe _ _ _ _
    (fun j e x => entryR D.P k W (first D.P (L0 + (2 * l' + 1)) + 6) (uGUr D.P) [j, e, x])
    fun e he => Eu_eq D k W hx he

include h0 in
/-- Panel Dr l'. -/
theorem TnPan_Dr (l' : ℕ) :
    (Pan.Dr l').TnPan D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ =
      (tnOf D tb L0 z zh ζ (.Dr l') 0).Tn D.P k W := by
  have hx : hasExperts (L0 + (2 * l' + 1)) := by
    unfold hasExperts
    omega
  show ∑ e ∈ range D.P.nexp, (Pan.Dr l').Er D ζ e * ∑ i ∈ range D.P.fe, (Pan.Dr l').Ec D ζ i *
      ∑ x ∈ range D.P.d, ew D z .D x * (layerR D.P k W (L0 + (2 * l' + 1))).Ed e i x =
    (⟨_, uDr D.P, [_, _, _]⟩ : TClaim K).Tn D.P k W
  rw [TClaim.Tn_three D.P k W _ (uDr D.P) _ _ _ rfl]
  exact sum_three D.P.nexp D.P.fe D.P.d _ _ _ _
    (fun j e x => entryR D.P k W (first D.P (L0 + (2 * l' + 1)) + 8) (uDr D.P) [j, e, x])
    fun e he => Ed_eq D k W hx he

/-! ## All weight panels -/

include h0 in
/-- The library's panels on the library's layout. For the weights that the library's layout reads in
a matrix W, from an even layer L0 on: the value of the tensor claim of row ρ of a weight panel with
two factors (TnRow) is the functional of the claim tnOf on W (TClaim.Tn). For every row number ρ. -/
theorem TnRow_Tn (hfe : D.fe ≤ D.f) (hh : D.P.nq + D.P.nkv ≤ 64) (p : Pan)
    (hw : p.weight = true) (h3 : p.three = false) (ρ : ℕ) :
    p.TnRow D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ ρ =
      (tnOf D tb L0 z zh ζ p ρ).Tn D.P k W := by
  cases p with
  | G => exact TnRow_G D r tb h0 k W z zh ζ ρ
  | U => exact TnRow_U D r tb h0 k W z zh ζ ρ
  | O => exact TnRow_O D r tb k W z zh ζ L0 ρ
  | D => exact TnRow_D D r tb h0 k W z zh ζ hfe ρ
  | V => exact TnRow_V D r tb k W z zh ζ L0 ρ
  | LR => exact TnRow_LR D r tb h0 k W z zh ζ ρ
  | QK => exact TnRow_QK D r tb L0 k W z zh ζ hh ρ
  | Gr l' => cases h3
  | Ur l' => cases h3
  | Dr l' => cases h3
  | N1 => cases hw
  | N2 => cases hw
  | XR => cases hw
  | DD => cases hw
  | MR => cases hw

include h0 in
/-- The same for a panel with three factors: the value of its one tensor claim (TnPan). -/
theorem TnPan_Tn (p : Pan) (h3 : p.three = true) :
    p.TnPan D r tb L0 (fun l => layerR D.P k W (L0 + l)) z zh ζ =
      (tnOf D tb L0 z zh ζ p 0).Tn D.P k W := by
  cases p with
  | Gr l' => exact TnPan_Gr D r tb h0 k W z zh ζ l'
  | Ur l' => exact TnPan_Ur D r tb h0 k W z zh ζ l'
  | Dr l' => exact TnPan_Dr D r tb h0 k W z zh ζ l'
  | G => cases h3
  | U => cases h3
  | O => cases h3
  | D => cases h3
  | V => cases h3
  | LR => cases h3
  | QK => cases h3
  | N1 => cases h3
  | N2 => cases h3
  | XR => cases h3
  | DD => cases h3
  | MR => cases h3

end Three

/-! ## The claims name units of the layout -/

section Units

variable (D : Dim) (tb : Tables) {L0 : ℕ} (h0 : L0 % 2 = 0) (z zh ζ : ℕ → K)

/-- The layer of the model to which row ρ of a weight panel belongs, counted from L0. -/
def layerOfRow : Pan → ℕ → ℕ
  | .LR, l' => 2 * l' + 1
  | .Gr l', _ => 2 * l' + 1
  | .Ur l', _ => 2 * l' + 1
  | .Dr l', _ => 2 * l' + 1
  | _, l => l

include h0 in
/-- The unit of the claim tnOf is the unit that the library's list of units has under the claim's
number, if the row's layer is a layer of the model. -/
theorem tnOf_unit (p : Pan) (hw : p.weight = true) (ρ : ℕ)
    (hL : L0 + layerOfRow p ρ < D.P.layers) :
    (units D.P)[(tnOf D tb L0 z zh ζ p ρ).n]? = some (tnOf D tb L0 z zh ζ p ρ).U := by
  have odd : ∀ l', hasExperts (L0 + (2 * l' + 1)) := fun l' => by
    unfold hasExperts
    omega
  have sh : ∀ l, (isExpL l = true ∧ hasExperts (L0 + l) ∧ fSh D l = D.P.fe) ∨
      (¬ isExpL l = true ∧ ¬ hasExperts (L0 + l) ∧ fSh D l = D.P.f) := fun l => by
    by_cases he : isExpL l = true
    · exact Or.inl ⟨he, (experts_iff h0 l).mpr he, if_pos he⟩
    · exact Or.inr ⟨he, fun hc => he ((experts_iff h0 l).mp hc), if_neg he⟩
  cases p with
  | V =>
    show (units D.P)[first D.P (L0 + ρ) + 1]? = some (uV D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits])
  | O =>
    show (units D.P)[first D.P (L0 + ρ) + 2]? = some (uO D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits])
  | QK =>
    show (units D.P)[first D.P (L0 + ρ)]? = some (uQK D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P (m := 0) hL (by simp [layerUnits])
  | LR =>
    show (units D.P)[first D.P (L0 + (2 * ρ + 1)) + 9]? = some (uR D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, odd ρ])
  | Gr l' =>
    show (units D.P)[first D.P (L0 + (2 * l' + 1)) + 5]? = some (uGUr D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, odd l'])
  | Ur l' =>
    show (units D.P)[first D.P (L0 + (2 * l' + 1)) + 6]? = some (uGUr D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, odd l'])
  | Dr l' =>
    show (units D.P)[first D.P (L0 + (2 * l' + 1)) + 8]? = some (uDr D.P)
    exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, odd l'])
  | G =>
    show (units D.P)[first D.P (L0 + ρ) + 3]? = some (uGU D.P (fSh D ρ))
    rcases sh ρ with ⟨_, hx, hf⟩ | ⟨_, hx, hf⟩
    · rw [hf]
      exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, hx])
    · rw [hf]
      exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, hx])
  | U =>
    show (units D.P)[first D.P (L0 + ρ) + 4]? = some (uGU D.P (fSh D ρ))
    rcases sh ρ with ⟨_, hx, hf⟩ | ⟨_, hx, hf⟩
    · rw [hf]
      exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, hx])
    · rw [hf]
      exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, hx])
  | D =>
    show (units D.P)[first D.P (L0 + ρ) + if isExpL ρ then 7 else 5]? =
      some (uD D.P (fSh D ρ))
    rcases sh ρ with ⟨he, hx, hf⟩ | ⟨he, hx, hf⟩
    · rw [if_pos he, hf]
      exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, hx])
    · rw [if_neg he, hf]
      exact Inst.Model.Layout.Bridge.unit_at D.P hL (by simp [layerUnits, hx])
  | N1 => cases hw
  | N2 => cases hw
  | XR => cases hw
  | DD => cases hw
  | MR => cases hw

end Units

/-! ## The hypotheses at the reference sizes -/

/-- The reference sizes have no more hidden units in an expert than in a layer. -/
theorem ref_fe : Dim.ref.fe ≤ Dim.ref.f := by decide

/-- Sizes that meet the library's Dim.OK have no more hidden units in an expert than in a layer. -/
theorem fe_of_ok {D : Dim} (hD : D.OK) : D.fe ≤ D.f := by
  have h := hD.f
  omega

/-- The reference sizes have at most 64 heads. -/
theorem ref_heads : Dim.ref.P.nq + Dim.ref.P.nkv ≤ 64 := by decide

#print axioms TnRow_Tn
#print axioms TnPan_Tn
#print axioms tnOf_unit
#print axioms ref_fe
#print axioms fe_of_ok
#print axioms ref_heads

end OnBytes.Road
