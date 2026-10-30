-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StartLine.lean: WHAT THE START FORM OF THE BATCHED SUMCHECK OF A LAYERS' SUB-PROOF
IS WORTH, WITH THE CALLS' AFFINE SHARES GATHERED AS THE TYPED LIBRARY's `lineS`
(Cb/Pv/Lay/At/Line.lean). A definition and five theorems. An identity between values: no draw, no
count.

Johnson/Road/FormsKeysWhole.lean (`start_whole`) sets the start form against the sum of the batched
sumcheck. The typed chain (Cb/Pv/Lay/At/Start.lean) writes its start claim otherwise: what the
lookup's end leaves, less the join's affine side `lineS`, less the hidden sum of the terms, plus the
drawn element times what the terms' sumcheck leaves. This file brings the verifier's form to that
shape, in every world and at all cells for which the eight factors are worth what
`joinPart_keyVec'` (Johnson/Road/FormsKeysShape.lean) says.

  `linesP D t tb L0 w c ζ`: one call's padding share and affine parts at a free point.
  `keyVec_lines`: the extension of a call's key vector is `linesP`, plus TSP, plus the sums ACCP.
  `lines_lineS`: if all eight calls' points and weights read as the library's at one z, and
    D.lT ≤ D.cap: the weighted sum of the eight `linesP` is `lineS D t tb L0 w z`.
  `start_lines`: then the start form is worth: the sum over q < 8 of weight e_q times
    (alpha - q theta), plus the padding trees' number, less the worth of the lookup's end form, less
    `lineS`, less the hidden value under the slot of the terms' claimed sum, plus om[1] times the
    worth of KT.
  `trueAt_noEntry`: a world all of whose entries of virtual rows are 0 has true tables of the cells
    0, whatever stands under its slots (`trueAt_zero`, Johnson/Road/K4/ZeroWorld.lean,
    for more worlds). So `start_lines` can be read at the world of what was shown, at the cells 0:
    there the left side is the form's public part, read.

Limits. hz and hwc are asked of ALL EIGHT calls (`start_whole` asks four). By FormsKeysWhole.lean's
own words they hold at the full-size shipped example and fail for call 0 at the small one. hp is a
premise, as in `start_whole`. What KT and the lookup's end form are worth is not looked at. That the
typed start target is this number is not concluded here.
-/
import Johnson.Road.FormsKeysWhole
import Johnson.Road.FormsKeysVec
import Johnson.Road.K4.ZeroWorld
import Cb.Pv.Lay.At.Line

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env Heard)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW aC zc wc keyVec famsIn lut)

section Lines
variable {K : Type} [Field K] (D : Dim) [scl : Scl] (t : Cell → K) (tb : Tables) (L0 : ℕ)
  (w : ℕ → LW K)

/-- One call's padding share and affine parts, at a free point. -/
def linesP (c : Fin 8) (ζ : ℕ → K) : K :=
  (((lut tb c).pad : ℤ) : K) * PADWP D c ζ +
    ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s => LINEP D t tb L0 w ζ s l).sum

/-- The extension of a call's key vector, in three parts. -/
theorem keyVec_lines (c : Fin 8) (ζ : ℕ → K) :
    Blocks.ext (aC D c) (keyVec D t tb L0 w c) ζ =
      linesP D t tb L0 w c ζ + TSP D t tb L0 w c ζ +
        ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s => ACCP D t w ζ s l).sum := by
  rw [ext_keyVec_KFP]
  have split : ∀ l, ((famsIn c l).map fun s =>
      LINEP D t tb L0 w ζ s l + ACCP D t w ζ s l).sum =
      ((famsIn c l).map fun s => LINEP D t tb L0 w ζ s l).sum +
        ((famsIn c l).map fun s => ACCP D t w ζ s l).sum := by
    intro l
    induction famsIn c l with
    | nil => simp
    | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  unfold KFP linesP
  simp only [split, mul_add, sum_add_distrib]
  ring

/-- **The eight calls' affine shares, under the calls' weights, are the typed library's.** -/
theorem lines_lineS (hcap : D.lT ≤ D.cap) (z : ℕ → K) (ζ : Fin 8 → ℕ → K) (e : Fin 8 → K)
    (hz : ∀ c : Fin 8, ∀ j, j < aC D c → ζ c j = zc D z c j) (hwc : ∀ c, e c = wc D z c) :
    ∑ c : Fin 8, e c * linesP D t tb L0 w c (ζ c) = Cb.Pv.Lay.At.lineS D t tb L0 w z := by
  unfold Cb.Pv.Lay.At.lineS linesP
  refine sum_congr rfl fun c _ => ?_
  have e1 : ∀ l, ((famsIn c l).map fun s => LINEP D t tb L0 w (ζ c) s l) =
      (famsIn c l).map fun s => Inst.Model.FFSeg.LINE D t tb L0 w z s l := fun l =>
    List.map_congr_left fun s hs => by
      have hc := call_of_famsIn hs
      rw [LINE_eq_LINEP D t tb L0 w hcap, hc]
      exact LINEP_congr D t tb L0 w hc (hz c) l
  simp only [e1, elP_eq_el D (hz c), PADWP_eq_PADW D (hz c), hwc c]

variable (ρ : Reading K)

/-- **The start form, with the affine side gathered.** -/
theorem start_lines (W : World K) (H : Heard) (om : Array E) (parts : List Aff) {tT : Model.Tsc}
    (hT : H.tT = some tT) (hlen : parts.length = 8) (alpha theta : E) (z : ℕ → K)
    (ζ : Fin 8 → ℕ → K)
    (hp : ∀ (c : Fin 8) (f : Aff), parts[c.val]? = some f →
      f.value ρ W = ρ.val alpha - (c.val : K) * ρ.val theta -
        Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c) + TSP D t tb L0 w c (ζ c) +
        ∑ l ∈ range D.nl, elP D (ζ c) l * ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum)
    (hcap : D.lT ≤ D.cap) (hz : ∀ c : Fin 8, ∀ j, j < aC D c → ζ c j = zc D z c j)
    (hwc : ∀ c : Fin 8, ρ.val (H.fo.e.getD c.val zeroE) = wc D z c) :
    (startOf H om parts).value ρ W =
      ∑ q ∈ range 8, ρ.val (H.fo.e.getD q zeroE) * (ρ.val alpha - (q : K) * ρ.val theta) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ W - Cb.Pv.Lay.At.lineS D t tb L0 w z -
        W.slot tT.sCl + ρ.val (om.getD 1 zeroE) * H.KT.value ρ W := by
  have hp' : ∀ x ∈ parts.zipIdx, x.1.value ρ W =
      (fun q : ℕ => ρ.val alpha - (q : K) * ρ.val theta) x.2 -
        onFin (fun c : Fin 8 => linesP D t tb L0 w c (ζ c)) x.2 + (fun _ : ℕ => (0 : K)) x.2 +
        (fun _ : ℕ => (0 : K)) x.2 := by
    rintro ⟨f, q⟩ hx
    have h1 : parts[q]? = some f := by simpa using List.mem_zipIdx_iff_getElem?.mp hx
    obtain ⟨hq, -⟩ := List.getElem?_eq_some_iff.mp h1
    rw [hlen] at hq
    have h2 := hp ⟨q, hq⟩ f h1
    show f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta - onFin _ q + 0 + 0
    rw [onFin_lt _ hq, h2, keyVec_lines]
    ring
  have key := start_parts ρ W H om parts hT (fun q : ℕ => ρ.val alpha - (q : K) * ρ.val theta)
    (onFin fun c : Fin 8 => linesP D t tb L0 w c (ζ c)) (fun _ => 0) (fun _ => 0) hp'
  rw [hlen] at key
  simp only [mul_sub, sum_sub_distrib, mul_zero, sum_const_zero] at key
  rw [sum_onFin, lines_lineS D t tb L0 w hcap z ζ _ hz hwc] at key
  rw [key]
  simp only [mul_sub, sum_sub_distrib]
  ring

end Lines

section NoEntry
variable {K : Type} [Field K] {ρ : Reading K}

theorem U3at_noEntry {W : World K} (hW : ∀ a b c, W.entry a b c = 0) {v : Env} {tb e : ℕ}
    {a : Aff} (h : v.U3at tb e = some a) : a.value ρ W = 0 := by
  obtain ⟨_, _, _, hv⟩ := U3at_entry ρ W h
  rw [hv]
  exact hW _ _ _

/-- **A world without entries has true tables of the cells 0.** -/
theorem trueAt_noEntry {W : World K} (hW : ∀ a b c, W.entry a b c = 0) (v : Env) (lT : ℕ)
    (low u : ℕ → K) : TrueAt ρ W v lT (fun _ _ _ => 0) low u :=
  have hS : ∀ tb mat, ShortTrue ρ W v tb mat lT (fun _ _ _ => 0) u := fun _ _ _ _ h => by
    rw [U3at_noEntry hW h, Blocks.ext_zero_of_forall (fun _ _ => rfl)]
  have hL : ∀ tb mat, LongTrue ρ W v tb mat v.y.ls lT (fun _ _ _ => 0) low u :=
    fun _ _ _ _ h => by
      rw [U3at_noEntry hW h]
      exact (sum_eq_zero fun r _ => by
        rw [Blocks.ext_zero_of_forall (fun _ _ => rfl), mul_zero]).symm
  { af := fun b _ => hL b 0
    qa := fun b _ => hL b 3
    xi := fun b _ => hL b 4
    xo := fun b _ => hL b 5
    ad := fun b _ => hS b 1
    ar := fun b _ => hS b 2 }

end NoEntry
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.keyVec_lines
#print axioms OnBytes.Road.K4.lines_lineS
#print axioms OnBytes.Road.K4.start_lines
#print axioms OnBytes.Road.K4.trueAt_noEntry
