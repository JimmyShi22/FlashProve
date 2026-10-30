-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesForms.lean: the layers' forms for the columns of the planes of their lookup's
counts, and why the law of the rows alone says nothing of what they are worth.

The layers' form for a column of the planes' matrix is one entry of the vector of reads, an array of
its own. Under the library's law of the rows (Fo.RowsLaw,
OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean) that entry is a combination of THAT array's cells,
whatever the cells of the planes' matrix are. So the law of the rows does not make the form worth
the column's combination of the planes' cells: where the caller's index set has a place for a cell
of that array, apart from the planes' cells, and the row's weight does not read as 0,
`counter_world` gives a world with the law of the rows in which the two differ. What lacks is the
law of the reads (Johnson/Meaning/PlanesLaw.lean).

Main names (namespace `Meaning.Planes`).
  `counter_world`: for a form that is one entry (a, e, i), and a row r₀ of the array a whose cell at
      i lies at another place than the array's other cells at i and than the cells of column col₀ of
      the planes' matrix: there are cells μ₀ and entries that MEET THE LAW OF THE ROWS, in which the
      form is worth row e's declared weight at r₀, and colsK at col₀ is 0.
  `counter_world_one`: the same for an array of one row under the weight 1, as the verifier's
      routine coefficientsF (OnBytes/Model/Tail.lean) lays the vector of reads: the form is worth 1.
  `k4Bit`, `k4Pin`: the layers' forms, with {} where there is none.
  `planeCol_ent`: where the layers have a form for a column, it is one entry of the vector of reads.

Limits. The premises on the places (en, pl) are letters here. A caller whose index set has no place
for the cells of the vector of reads has no such world; of such a caller this file says nothing.
In `counter_world_one` the two sides, 1 and 0, differ only in a ring with 0 ≠ 1. No statement is
refuted in this file: it gives the world. Nothing on soundness.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoRowsLaw
import OnBytes.Tie.Pv.Lookup.Forest.FoNumsEq
import OnBytes.Tie.Pv.Lookup.Forest.FoPlaneRows
import OnBytes.Tie.Pv.Lookup.Forest.FoPin
import OnBytes.Tie.Pv.Lookup.Port.FoReads
import OnBytes.Tie.Pv.Led.LedWalkPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open Finset
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open Cb.Fo.Pin

variable {K J₀ : Type} [CommRing K] [DecidableEq J₀]

/-- **A world that meets the law of the rows and parts the two sides.** μ₀ is 1 at the place of cell
(r₀, i) of the array a and 0 elsewhere; each entry of a virtual row is what the law of the rows
makes of μ₀. -/
theorem counter_world (ρ : Reading K) (Fw H : Fork) (h : FoNums.Sh) (lm : ℕ) (zb0 : List K)
    (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (en : ℕ × ℕ × ℕ → J₀) (col₀ a e i r₀ : ℕ)
    (hr₀ : r₀ < (Fw.trees.getD a {}).R)
    (inj : ∀ r < (Fw.trees.getD a {}).R, r ≠ r₀ → en (a, r, i) ≠ en (a, r₀, i))
    (apart : ∀ row < 2 ^ lm, pl row col₀ ≠ en (a, r₀, i)) :
    ∃ (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K),
      _root_.Fo.RowsLaw ρ Fw (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
        (fun t r i => μ₀ (en (t, r, i))) ∧
      (Aff.ent a e i).value ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) =
        ρ.val ((rowAt Fw a e).coef.getD r₀ zeroE) ∧
      colsK h lm zb0 (fun p => zext μ₀ (placeOf mk pl p)) col₀ = 0 := by
  refine ⟨fun j => if j = en (a, r₀, i) then 1 else 0, fun t' e' i' =>
    ∑ r ∈ range (Fw.trees.getD t' {}).R, ρ.val ((rowAt Fw t' e').coef.getD r zeroE) *
      (if en (t', r, i') = en (a, r₀, i) then 1 else 0), fun _ _ _ _ => rfl, ?_, ?_⟩
  · rw [Aff.value_ent]
    show ∑ r ∈ range (Fw.trees.getD a {}).R, ρ.val ((rowAt Fw a e).coef.getD r zeroE) *
      (if en (a, r, i) = en (a, r₀, i) then 1 else 0) = _
    rw [Finset.sum_eq_single r₀]
    · rw [if_pos rfl, mul_one]
    · intro r hr hne
      rw [if_neg (inj r (mem_range.mp hr) hne), mul_zero]
    · intro hn
      exact absurd (mem_range.mpr hr₀) hn
  · unfold colsK
    refine Finset.sum_eq_zero fun row hrow => ?_
    show _ * (if pl row col₀ = en (a, r₀, i) then (1 : K) else 0) = 0
    rw [if_neg (apart row (mem_range.mp hrow)), mul_zero]

/-- The same for an array of one row whose virtual row e has the weight 1: the form is worth 1. -/
theorem counter_world_one (ρ : Reading K) (Fw H : Fork) (h : FoNums.Sh) (lm : ℕ) (zb0 : List K)
    (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (en : ℕ × ℕ × ℕ → J₀) (col₀ a e i : ℕ)
    (hR : (Fw.trees.getD a {}).R = 1) (hc : (rowAt Fw a e).coef = #[oneE])
    (apart : ∀ row < 2 ^ lm, pl row col₀ ≠ en (a, 0, i)) :
    ∃ (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K),
      _root_.Fo.RowsLaw ρ Fw (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
        (fun t r i => μ₀ (en (t, r, i))) ∧
      (Aff.ent a e i).value ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) = 1 ∧
      colsK h lm zb0 (fun p => zext μ₀ (placeOf mk pl p)) col₀ = 0 := by
  obtain ⟨μ₀, entry, a1, a2, a3⟩ := counter_world ρ Fw H h lm zb0 mk pl en col₀ a e i 0
    (by rw [hR]; exact Nat.one_pos) (fun r hr hne => by rw [hR] at hr; omega) apart
  refine ⟨μ₀, entry, a1, ?_, a3⟩
  rw [a2, hc]
  exact ρ.one

/-- The layers' form for column col of the planes' matrix at the leaves' point (e = 0) or the bits'
point, as the lookup's law reads a caller's forms: {} where there is none. -/
def k4Bit (v : Layer.Env) (tB0 tB1 e col : ℕ) : Aff :=
  (Road.Rows.planeCol v (if e == 0 then tB0 else tB1) col).getD {}

/-- The layers' form for the counts of column col. -/
def k4Pin (v : Layer.Env) (tP col : ℕ) : Aff := (Road.Rows.planeCol v tP col).getD {}

/-- Where the layers have a form for a column, it is one entry of the vector of reads. -/
theorem planeCol_ent {v : Layer.Env} {t col : ℕ} {b : Aff}
    (h : Road.Rows.planeCol v t col = some b) :
    b = Aff.ent v.iU3 ((t + col) / v.K3) ((t + col) % v.K3) := by
  unfold Road.Rows.planeCol at h
  split at h
  · exact U3at_some v t col b h
  · cases h

#print axioms counter_world
#print axioms counter_world_one
#print axioms planeCol_ent

end Meaning.Planes
