-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Bits.lean: the sumcheck for the bits of the index of an attention segment, for any number
of variables that number a bit.

The library's step s21 of an attention segment (Inst/Model/Att/Sums.lean) runs over the cube
(position | head | number of a bit). For the number of a bit it takes as many variables as the
number of bits of a position needs (lK). The programs bind 4 variables at every size. The two agree
for requests of 2^9 to 2^16 tokens. This file writes the step's first map, its public weight and its
sum with a free number kap in the place of lK.

Main names:
  bitCube kap D t b: the first map on the cube: a bit of the index of pair b, and 0 from the number
    lT on. The second map is the first minus 1.
  bitWt kap D p b: the public weight, a polynomial in the point.
  bitSum kap D p t: the sum over the vertices of the cube and the pairs.
  bitCube_lK, bitWt_lK: at kap = lK the map and the weight are the library's, by definition.

Limits. Definitions and two equations that hold by definition. Nothing is said on a verifier, on an
honest prover or on hiding.


-/
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset
open Inst.Model.AttSeg

variable {K : Type} [Field K]

/-- The first map of the sumcheck for the bits, on the cube (position | head | number of a bit) with
kap variables for the number: that bit of the index of pair b, and 0 from the number lT on. -/
def bitCube (kap : ℕ) (D : Dim) (t : Raw → K) (b X : ℕ) : K :=
  if X % 2 ^ kap < D.lT then ibV t (X % 2 ^ kap) b (X / 2 ^ kap % D.nG) (X / 2 ^ kap / D.nG) else 0

/-- The public weight of pair b at the point ξ = (ξ_i | ξ_g | ξ_k). -/
def bitWt (kap : ℕ) (D : Dim) (p : Pub K) (b : ℕ) (ξ : ℕ → K) : K :=
  p.o'' b * eqPt D.lT p.tbi ξ * eqPt D.lg p.tbg (sh ξ D.lT) * eqPt kap p.tk (sh ξ (D.lT + D.lg))

/-- The sum of the sumcheck: over the vertices of the cube and the pairs, the weight times the first
map times the first map minus 1. -/
def bitSum (kap : ℕ) (D : Dim) (p : Pub K) (t : Raw → K) : K :=
  ∑ X ∈ range (2 ^ (D.lT + D.lg + kap)), ∑ b ∈ range D.nb,
    bitWt kap D p b (Blocks.cubePt (D.lT + D.lg + kap) X) * bitCube kap D t b X *
      (bitCube kap D t b X - 1)

/-- With the library's number of variables the map is the library's. -/
theorem bitCube_lK (D : Dim) (C : Calls) (p : Pub K) (t : Raw → K) (b : ℕ) :
    bitCube D.lK D t b = Acube D C p t .s21 b := rfl

/-- With the library's number of variables the weight is the library's. -/
theorem bitWt_lK (D : Dim) (C : Calls) (p : Pub K) (b : ℕ) :
    bitWt D.lK D p b = Wb D C p .s21 b := rfl

end Cb.Pv.Att
