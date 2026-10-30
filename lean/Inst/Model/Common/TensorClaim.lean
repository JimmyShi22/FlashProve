-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Common/TensorClaim.lean: a tensor claim on the matrix W, indexed by ℕ. Definitions, first
lemmas.

 * `boxSum`: the sum over the index tuples of a list of coordinates, with one factor for each
   coordinate.
 * `TClaim`: the number of the unit (a weight tensor, `Layout.UnitS`) in the order of
   Inst/Model/Layout.lean, the unit, and one factor for each coordinate, in the order of the
   coordinates of the unit. A factor is a function on ℕ, of which only the values below the size of
   the coordinate count ("restricted to the actual size").
 * `TClaim.Tn`: the functional, for a matrix W over any commutative ring, a function on ℕ × ℕ.
The condition that the factors are products over the split (`SplitOK`), and the form in which the
merge of tensor claims takes a claim (`MG.TLay`, Blocks/MergeBlock.lean):
Inst/Model/LayoutTensor.lean.

Notation: `E`: a commutative ring; `W`: a map ℕ → ℕ → E, the matrix; `P`: `Params`, "The parameters
of the program" (Inst/Model/Program.lean); `k`: a natural number, the first argument of
`Layout.place`; `U`: a `Layout.UnitS`: "A unit U is W[i_1, ..., i_n] with i_g < R_g ..., stored in
n_U ∈ {2, 4} bytes" (Inst/Model/Layout.lean); `U.nU`: n_U; `Layout.place`: "Byte ȷ of entry i is in
row o_U + row_U(ȷ, i^r) and column col_U(i^c)" (there); W_W[i]: `entryW P k W n U i`, see its
docstring; Tn_a(W): `a.Tn P k W`.
-/
import Inst.Model.Layout
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Inst.Model

open Finset

variable {E : Type} [CommRing E]

/-- Σ over the tuples (i_1, .., i_n), i_g < R_g, of Π_g f_g[i_g] · F(i) -/
def boxSum : List Layout.Coord → List (ℕ → E) → (List ℕ → E) → E
  | [], _, F => F []
  | c :: cs, f :: fs, F => ∑ i ∈ range c.R, f i * boxSum cs fs fun is => F (i :: is)
  | _ :: _, [], _ => 0

/-- A tensor claim, without its masked scalar. -/
structure TClaim (E : Type) where
  /-- the number of the unit in the order of the units -/
  n : ℕ
  U : Layout.UnitS
  /-- one factor for each coordinate -/
  f : List (ℕ → E)

/-- the entry i of the unit U with the number n that the matrix W holds: Σ_ȷ 256^ȷ W[row][column] -/
def entryW (P : Params) (k : ℕ) (W : ℕ → ℕ → E) (n : ℕ) (U : Layout.UnitS) (i : List ℕ) : E :=
  ∑ jj ∈ range U.nU, 256 ^ jj *
    W (Layout.place k (Layout.units P) n U jj i).1 (Layout.place k (Layout.units P) n U jj i).2

/-- The functional of a tensor claim: Tn_a(W) = Σ_i Π_g f_g[i_g] W_W[i] (`entryW`). -/
def TClaim.Tn (P : Params) (k : ℕ) (W : ℕ → ℕ → E) (a : TClaim E) : E :=
  boxSum a.U.coords a.f fun i => entryW P k W a.n a.U i

theorem boxSum_two (c₁ c₂ : Layout.Coord) (f₁ f₂ : ℕ → E) (F : List ℕ → E) :
    boxSum [c₁, c₂] [f₁, f₂] F = ∑ i ∈ range c₁.R, ∑ j ∈ range c₂.R, f₁ i * f₂ j * F [i, j] := by
  simp only [boxSum, mul_sum, mul_assoc]

theorem boxSum_three (c₁ c₂ c₃ : Layout.Coord) (f₁ f₂ f₃ : ℕ → E) (F : List ℕ → E) :
    boxSum [c₁, c₂, c₃] [f₁, f₂, f₃] F =
      ∑ i ∈ range c₁.R, ∑ j ∈ range c₂.R, ∑ l ∈ range c₃.R, f₁ i * f₂ j * f₃ l * F [i, j, l] := by
  simp only [boxSum, mul_sum, mul_assoc]

/-- A claim on a unit with two coordinates. -/
theorem TClaim.Tn_two (P : Params) (k : ℕ) (W : ℕ → ℕ → E) (n : ℕ) (U : Layout.UnitS)
    (c₁ c₂ : Layout.Coord) (hU : U.coords = [c₁, c₂]) (f₁ f₂ : ℕ → E) :
    (⟨n, U, [f₁, f₂]⟩ : TClaim E).Tn P k W =
      ∑ i ∈ range c₁.R, ∑ j ∈ range c₂.R, f₁ i * f₂ j * entryW P k W n U [i, j] := by
  show boxSum U.coords [f₁, f₂] _ = _
  rw [hU, boxSum_two]

/-- A claim on a unit with three coordinates. -/
theorem TClaim.Tn_three (P : Params) (k : ℕ) (W : ℕ → ℕ → E) (n : ℕ) (U : Layout.UnitS)
    (c₁ c₂ c₃ : Layout.Coord) (hU : U.coords = [c₁, c₂, c₃]) (f₁ f₂ f₃ : ℕ → E) :
    (⟨n, U, [f₁, f₂, f₃]⟩ : TClaim E).Tn P k W =
      ∑ i ∈ range c₁.R,
        ∑ j ∈ range c₂.R, ∑ l ∈ range c₃.R, f₁ i * f₂ j * f₃ l * entryW P k W n U [i, j, l] := by
  show boxSum U.coords [f₁, f₂, f₃] _ = _
  rw [hU, boxSum_three]

end Inst.Model
