-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PanelSides.lean: what it says that one panel of the verifier's batched sumcheck has,
side by side and place by place, the form parts of a panel of the library; and four general lemmas
that conclude it from a panel's fields.

Johnson/Road/FormsKeysEarly.lean and FormsKeysLate.lean compare, kind of panel by kind, the SHARES:
sums of products of the two sides. The library's typed batched sumcheck
(Cb/Pv/Lay/At/Inner.lean) wants each side by itself, as far as it is a form in the cells. Here the
never-sent vectors and the vectors of the weight claims are set to 0 (Johnson/Road/K4/FormParts.lean
says why that is what the two forms Alin and Blin are worth).

Main names:
  `SidesAre`: the panel b has the bits of the library's panel pn; its A side, with all the factors
    that the verifier computes, is pn.om x * wc * pn.wt * pn.A on the rows and columns of pn and 0
    elsewhere, or 0 everywhere if the A side of pn is a never-sent vector; its B side is pn.B there
    and 0 elsewhere, or 0 everywhere if the B side of pn is a weight matrix.
  `omK_om`: the weight of the panel's claim.
  `sides_weight_forms`: a panel with two factors, A side forms, B side a weight matrix.
  `sides_forms`: a panel with two factors, both sides forms.
  `sides_tri_forms`: a panel with the selector whose column factor is given as forms.
  `sides_virt`: a panel whose A side holds a never-sent vector.
Limits. Definitions and identities in one world. Every lemma asks the panel's fields and what its
forms and weights are worth as premises; nothing here shows them of a panel that the verifier
appends. Nothing on a run, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysPort
import Johnson.Road.FormsKeysPos
import Cb.Pv.Lay.At.InnerGeo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Lay SBlk)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim LW Pan Rd wc call)
open Cb.Pv.Lay.At (isVirt)

variable {K : Type} [Field K]

section Def
variable [scl : Scl]

/-- The panel b has the bits and, side by side, the form parts of the library's panel pn. x: the
weight of claim 1. -/
structure SidesAre (ρ : Reading K) (W : World K) (y : Lay) (om : Array E) (D : Dim) (r : Rd K)
    (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K) (x : K) (b : SBlk) (pn : Pan) : Prop where
  /-- the bits of a place -/
  bw : b.w = pn.wid D
  /-- the bits of a column -/
  bwy : b.wy = pn.wcol D
  /-- the A side without the never-sent vectors -/
  sa : ∀ i yv, aG ρ W y om (fun _ _ => 0) b i yv =
    if isVirt pn = true then 0 else
      if i < pn.nr D ∧ yv < pn.nc D then
        pn.om x * wc D z (call pn.fam) * pn.wt D z i * pn.A D r i yv else 0
  /-- the B side without the vectors of the weight claims -/
  sb : ∀ i yv, bG ρ W (fun _ _ => 0) b i yv =
    if pn.weight = true then 0 else
      if i < pn.nr D ∧ yv < pn.nc D then pn.B D r tb L0 w z zh i yv else 0

end Def

/-- The weight of the panel's claim is the library's. -/
theorem omK_om {ρ : Reading K} {om : Array E} {b : SBlk} {pn : Pan}
    (hcl : b.claim = if pn.late then 1 else 0) (hom : ρ.val (om.getD 0 zeroE) = 1) :
    omK ρ om b = pn.om (ρ.val (om.getD 1 zeroE)) := by
  unfold omK Pan.om
  rw [hcl]
  cases pn.late
  · simp only [Bool.false_eq_true, if_false, hom]
  · simp only [if_true]

/-- The bits of a panel from its rows and columns. -/
theorem bits_of {D : Dim} {b : SBlk} {pn : Pan} {n : ℕ} (hn : n = pn.nr D)
    (hny : b.ny = pn.nc D) (hwy : b.wy = ceilLog2 b.ny) (hw : b.w = ceilLog2 n + b.wy) :
    b.w = pn.wid D ∧ b.wy = pn.wcol D := by
  have e : b.wy = pn.wcol D := by
    rw [hwy, hny, ceilLog2_eq_clog]
    rfl
  refine ⟨?_, e⟩
  rw [hw, e, hn, ceilLog2_eq_clog]
  rfl

section Lemmas
variable [scl : Scl] {ρ : Reading K} {W : World K} {y : Lay} {om : Array E} {D : Dim} {r : Rd K}
  {tb : Tables} {L0 : ℕ} {w : ℕ → LW K} {z zh : ℕ → K} {x : K} {b : SBlk} {pn : Pan}

/-- A panel with two factors: A side forms, B side a weight matrix. -/
theorem sides_weight_forms (hv : isVirt pn = false) (hg : pn.weight = true) (ht : b.tri = false)
    (hk : b.virt = none) {v0 : ℕ} (h0 : b.v0 = some v0) {Af : ℕ → ℕ → Option Aff}
    (hAf : b.A = some Af) (hr : Returns b) (hni : b.ni = pn.nr D) (hny : b.ny = pn.nc D)
    (hwy : b.wy = ceilLog2 b.ny) (hw : b.w = ceilLog2 b.ni + b.wy) (hom : omK ρ om b = pn.om x)
    (hec : ρ.val b.ec = wc D z (call pn.fam)) (hwt : ∀ i, i < pn.nr D → wtK ρ b i = pn.wt D z i)
    (hA : ∀ i yv a, Af i yv = some a → a.value ρ W = pn.A D r i yv) :
    SidesAre ρ W y om D r tb L0 w z zh x b pn := by
  obtain ⟨e1, e2⟩ := bits_of hni hny hwy hw
  refine ⟨e1, e2, fun i yv => ?_, fun i yv => ?_⟩
  · unfold aG
    rw [ht, hk, hv, hni, hny]
    simp only [Bool.false_eq_true, if_false]
    by_cases h1 : i < pn.nr D
    · by_cases h2 : yv < pn.nc D
      · obtain ⟨a, ha⟩ := hr.1 Af hAf i (hni ▸ h1) yv (hny ▸ h2)
        rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, hom, hec, hwt i h1]
        unfold sideK ov
        rw [hAf]
        simp only [ha]
        rw [hA i yv a ha]
      · rw [if_pos h1, if_neg h2, if_neg fun c => h2 c.2]
    · rw [if_neg h1, if_neg fun c => h1 c.1]
  · unfold bG
    rw [ht, hk, h0, hg]
    simp

/-- A panel with two factors, both sides forms. -/
theorem sides_forms (hv : isVirt pn = false) (hg : pn.weight = false) (ht : b.tri = false)
    (hk : b.virt = none) (h0 : b.v0 = none) {Af Bf : ℕ → ℕ → Option Aff} (hAf : b.A = some Af)
    (hBf : b.B = some Bf) (hr : Returns b) (hni : b.ni = pn.nr D) (hny : b.ny = pn.nc D)
    (hwy : b.wy = ceilLog2 b.ny) (hw : b.w = ceilLog2 b.ni + b.wy) (hom : omK ρ om b = pn.om x)
    (hec : ρ.val b.ec = wc D z (call pn.fam)) (hwt : ∀ i, i < pn.nr D → wtK ρ b i = pn.wt D z i)
    (hA : ∀ i yv a, i < pn.nr D → yv < pn.nc D → Af i yv = some a →
      a.value ρ W = pn.A D r i yv)
    (hB : ∀ i yv a, i < pn.nr D → yv < pn.nc D → Bf i yv = some a →
      a.value ρ W = pn.B D r tb L0 w z zh i yv) :
    SidesAre ρ W y om D r tb L0 w z zh x b pn := by
  obtain ⟨e1, e2⟩ := bits_of hni hny hwy hw
  refine ⟨e1, e2, fun i yv => ?_, fun i yv => ?_⟩
  · unfold aG
    rw [ht, hk, hv, hni, hny]
    simp only [Bool.false_eq_true, if_false]
    by_cases h1 : i < pn.nr D
    · by_cases h2 : yv < pn.nc D
      · obtain ⟨a, ha⟩ := hr.1 Af hAf i (hni ▸ h1) yv (hny ▸ h2)
        rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, hom, hec, hwt i h1]
        unfold sideK ov
        rw [hAf]
        simp only [ha]
        rw [hA i yv a h1 h2 ha]
      · rw [if_pos h1, if_neg h2, if_neg fun c => h2 c.2]
    · rw [if_neg h1, if_neg fun c => h1 c.1]
  · unfold bG
    rw [ht, hk, h0, hg, hni, hny]
    simp only [Bool.false_eq_true, if_false]
    by_cases h1 : i < pn.nr D
    · by_cases h2 : yv < pn.nc D
      · obtain ⟨a, ha⟩ := hr.2 Bf hBf i (hni ▸ h1) yv (hny ▸ h2)
        rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
        unfold sideK ov
        rw [hBf]
        simp only [ha]
        rw [hB i yv a h1 h2 ha]
      · rw [if_pos h1, if_neg h2, if_neg fun c => h2 c.2]
    · rw [if_neg h1, if_neg fun c => h1 c.1]

/-- A panel with the selector whose column factor is given as forms. -/
theorem sides_tri_forms (hv : isVirt pn = false) (hg : pn.weight = true) (ht : b.tri = true)
    (hk : b.virt = none) {v0 : ℕ} (h0 : b.v0 = some v0) (hne : y.h.NE = pn.nr D)
    (hny : b.ny = pn.nc D) (hwy : b.wy = ceilLog2 b.ny)
    (hw : b.w = ceilLog2 (max y.h.NE 1) + b.wy) (hmax : ceilLog2 (max y.h.NE 1) = ceilLog2 y.h.NE)
    (hom : omK ρ om b = pn.om x) (hec : ρ.val b.ec = wc D z (call pn.fam))
    (hA : ∀ i yv, i < pn.nr D → yv < pn.nc D →
      wtK ρ b 0 * ρ.val (b.sl.getD i zeroE) * (b.xx.getD yv {}).value ρ W =
        pn.wt D z i * pn.A D r i yv) :
    SidesAre ρ W y om D r tb L0 w z zh x b pn := by
  obtain ⟨e1, e2⟩ := bits_of hne hny hwy (by rw [hw, hmax])
  refine ⟨e1, e2, fun i yv => ?_, fun i yv => ?_⟩
  · unfold aG
    rw [ht, hk, hv, hne, hny]
    simp only [Bool.false_eq_true, if_false]
    by_cases h1 : i < pn.nr D
    · by_cases h2 : yv < pn.nc D
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, hom, hec]
        linear_combination (pn.om x * wc D z (call pn.fam)) * hA i yv h1 h2
      · rw [if_pos h1, if_neg h2, if_neg fun c => h2 c.2]
    · rw [if_neg h1, if_neg fun c => h1 c.1]
  · unfold bG
    rw [ht, h0, hg]
    simp

/-- A panel whose A side holds a never-sent vector and whose B side is a weight matrix. n: its
rows. -/
theorem sides_virt (hv : isVirt pn = true) (hg : pn.weight = true) {k v0 : ℕ}
    (hk : b.virt = some k) (h0 : b.v0 = some v0) {n : ℕ} (hn : n = pn.nr D)
    (hny : b.ny = pn.nc D) (hwy : b.wy = ceilLog2 b.ny) (hw : b.w = ceilLog2 n + b.wy) :
    SidesAre ρ W y om D r tb L0 w z zh x b pn := by
  obtain ⟨e1, e2⟩ := bits_of hn hny hwy hw
  refine ⟨e1, e2, fun i yv => ?_, fun i yv => ?_⟩
  · unfold aG
    rw [hk, hv]
    cases b.tri <;> simp
  · unfold bG
    rw [hk, h0, hg]
    cases b.tri <;> simp

end Lemmas

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.sides_weight_forms
#print axioms OnBytes.Road.K4.sides_forms
#print axioms OnBytes.Road.K4.sides_tri_forms
#print axioms OnBytes.Road.K4.sides_virt
