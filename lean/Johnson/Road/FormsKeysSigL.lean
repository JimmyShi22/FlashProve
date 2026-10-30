-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysSigL.lean: the late panels' shares are affine in three families of the values
that they read: the library with itself.

Inst/Model/FF/Objects.lean defines the panels of the batched inner-product sumcheck through a
record Rd of the values that they read, a panel's share, and Sig1, the sum of the shares of the
late panels. Three fields of the record are the contractions of the norms' reciprocals (R2), of the
scores (sc2) and of the selectors' entries (sel2) at the end point of the sumcheck over the
positions. This file shows how Sig1 hangs on these three: in each late panel at most one of them
stands in the A side, to the first power, and none in the B side; the panel QK reads none.

Every statement here compares objects of the library with objects of the library. The file imports
no file of OnBytes/.

Main definitions: withEnds. Main theorems: sig1_affine; share_lin, share_QK_ends; late_pans.

There is no hypothesis: sig1_affine holds for all sizes, every record, all weights, tables and
points, and all values of the three families.

What is not claimed. Nothing is said of what Sig1 is worth, or of which values a prover sends. The
program does not import this file.
-/
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim LW Pan Rd pans Sig1)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A share whose A side is a sum of two, the second under a factor. -/
theorem lin_sums (c : K) (n m : ℕ) (wt : ℕ → K) (A Ah Am B : ℕ → ℕ → K) (β : K)
    (h : ∀ ρ ι, A ρ ι = Ah ρ ι + β * Am ρ ι) :
    c * ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, A ρ ι * B ρ ι =
      c * ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, Ah ρ ι * B ρ ι +
        β * (c * ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, Am ρ ι * B ρ ι) := by
  have e1 : ∀ ρ, ∑ ι ∈ range m, A ρ ι * B ρ ι =
      ∑ ι ∈ range m, Ah ρ ι * B ρ ι + β * ∑ ι ∈ range m, Am ρ ι * B ρ ι := by
    intro ρ
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ι _ => by rw [h]; ring
  have e2 : ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, A ρ ι * B ρ ι =
      ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, Ah ρ ι * B ρ ι +
        β * ∑ ρ ∈ range n, wt ρ * ∑ ι ∈ range m, Am ρ ι * B ρ ι := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ρ _ => by rw [e1]; ring
  rw [e2]
  ring

/-- A sum over a list of terms that are each a sum of two, the second under a factor. -/
theorem list_lin {α : Type} (f fh fm : α → K) (β : K) : ∀ l : List α,
    (∀ x ∈ l, f x = fh x + β * fm x) → (l.map f).sum = (l.map fh).sum + β * (l.map fm).sum
  | [], _ => by simp
  | x :: l, h => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      h x List.mem_cons_self, list_lin f fh fm β l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    ring

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

/-! ## The three families -/

/-- The record r with other contractions of the reciprocals, the scores and the selectors'
entries. -/
def withEnds (r : Rd K) (R2 sc2 : ℕ → K) (sel2 : ℕ → ℕ → K) : Rd K :=
  { r with R2 := R2, sc2 := sc2, sel2 := sel2 }

section Late

variable [scl : Scl] (D : Dim) (r : Rd K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)

/-- The panel QK reads none of the three. -/
theorem share_QK_ends (R2 sc2 : ℕ → K) (sel2 : ℕ → ℕ → K) :
    Pan.QK.share D (withEnds r R2 sc2 sel2) tb L0 w z zh = Pan.QK.share D r tb L0 w z zh := rfl

variable (Rh Rm sh sm : ℕ → K) (eh em : ℕ → ℕ → K) (β : K)

/-- The share of a late panel other than QK is linear in the three families. -/
theorem share_lin (p : Pan) (hl : p.late = true) (hq : p ≠ .QK) :
    p.share D (withEnds r (fun ν => Rh ν + β * Rm ν) (fun l => sh l + β * sm l)
        (fun l e => eh l e + β * em l e)) tb L0 w z zh =
      p.share D (withEnds r Rh sh eh) tb L0 w z zh +
        β * p.share D (withEnds r Rm sm em) tb L0 w z zh := by
  unfold Pan.share
  cases p with
  | G | U | O | D | V | LR => cases hl
  | QK => exact absurd rfl hq
  | N1 | N2 | XR | DD | MR => exact lin_sums _ _ _ _ _ _ _ _ β fun _ _ => rfl
  | Gr l' | Ur l' =>
    refine lin_sums _ _ _ _ _ _ _ _ β fun ρ ι => ?_
    show (eh l' ρ + β * em l' ρ) * r.xr2 l' ι =
      eh l' ρ * r.xr2 l' ι + β * (em l' ρ * r.xr2 l' ι)
    ring
  | Dr l' =>
    refine lin_sums _ _ _ _ _ _ _ _ β fun ρ ι => ?_
    show (eh l' ρ + β * em l' ρ) * r.hh2 l' ι =
      eh l' ρ * r.hh2 l' ι + β * (em l' ρ * r.hh2 l' ι)
    ring

/-- Sig1 is affine in the three families: at hidden values plus β times masks it is Sig1 at the
hidden values, plus β times its linear part at the masks, which is Sig1 at the masks less the share
of the panel QK. -/
theorem sig1_affine :
    Sig1 D (withEnds r (fun ν => Rh ν + β * Rm ν) (fun l => sh l + β * sm l)
        (fun l e => eh l e + β * em l e)) tb L0 w z zh =
      Sig1 D (withEnds r Rh sh eh) tb L0 w z zh +
        β * (Sig1 D (withEnds r Rm sm em) tb L0 w z zh - Pan.QK.share D r tb L0 w z zh) := by
  have L : ∀ p : Pan, p.late = true → p ≠ .QK → _ := share_lin D r tb L0 w z zh Rh Rm sh sm eh em β
  have B : ∀ f : ℕ → Pan, (∀ n, (f n).late = true) → (∀ n, f n ≠ .QK) → ∀ l : List ℕ, _ :=
    fun f h1 h2 l => list_lin
      (fun p : Pan => p.share D (withEnds r (fun ν => Rh ν + β * Rm ν) (fun l => sh l + β * sm l)
        (fun l e => eh l e + β * em l e)) tb L0 w z zh)
      (fun p : Pan => p.share D (withEnds r Rh sh eh) tb L0 w z zh)
      (fun p : Pan => p.share D (withEnds r Rm sm em) tb L0 w z zh) β (l.map f) fun p hp => by
        obtain ⟨n, -, rfl⟩ := List.mem_map.mp hp
        exact L _ (h1 n) (h2 n)
  unfold Sig1
  rw [late_pans D]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  rw [B Pan.Gr (fun _ => rfl) (fun _ => by simp), B Pan.Ur (fun _ => rfl) (fun _ => by simp),
    B Pan.Dr (fun _ => rfl) (fun _ => by simp), L .N1 rfl (by simp), L .N2 rfl (by simp),
    L .XR rfl (by simp), L .DD rfl (by simp), L .MR rfl (by simp), share_QK_ends, share_QK_ends,
    share_QK_ends]
  ring

end Late

#print axioms late_pans
#print axioms share_lin
#print axioms sig1_affine

end OnBytes.Road
