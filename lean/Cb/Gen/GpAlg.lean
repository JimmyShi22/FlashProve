-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/GpAlg.lean: the grand product by a product tree: its plain mathematics, without any
protocol. Definitions and statements (the proofs: Cb/Gen/GpAlgProofs.lean).

The objects. 2^g products of 2^n factors each. The factors are one vector A with the index (b|θ) =
b 2^g + θ, high bits first: b numbers the factor, θ the product. The levels are
`Blocks.lvl g n A l` (Blocks/LookupRel.lean): level n is A, for l < n an entry of level l is the
product of the two entries of level l + 1 above it (top bit 0 and 1), level 0 holds the products.
Vectors are functions on ℕ, points are sequences, sizes are numbers: no type depends on a size.
`ext k v z` is the value at z of the multilinear extension of the first 2^k entries of v.
The chain of claims. Rel (every product has its target) → Claim 0 → Claim 1 → .. → Claim n, where
Claim l says that the extension of level l has the value t at the point z.

Main names:
  rel_iff_zero, zero_iff_claim0 what a zerocheck is run on, and that its output is Claim 0 at the
    target ext g h z
  `Spec.claim_iff_sum`: for l < n, Claim l is the sum over the cube of the equality factor times
    the product of the two halves of level l + 1: the input of a sumcheck.
  `Spec.line_defect`, `Spec.cnt_line_le_one`: the line step, for any vector: two claims on the
    halves at a point r become one claim at (c | r); the defect of the new claim is (1 - c) e₀ + c
    e₁, e₀ and e₁ the defects of the two; at most one value of c is bad.
  `Spec.line_claim`: what joins the line step to the levels.
  `Spec.claim_top`: Claim n is a claim on the factors.

Targets are plain elements here: a target that stands in an oracle or behind a mask is, at a fixed
message, an element.
Limits: this file says nothing on the zerocheck and the sumchecks themselves, and nothing on
oracles, masks, codes.

The product tree with one sumcheck a level is the field's; the protocol of this protocol's technical
report, which follows the texts named in lean/CREDITS.md, uses it in this form.
-/
import Blocks.LookupRel
import Blocks.ProductBlock

set_option autoImplicit false

namespace Cb.Gp
open Blocks Finset

variable {E : Type} [Field E]

/-- Every product has its target. -/
def Rel (g n : ℕ) (A h : ℕ → E) : Prop := ∀ θ < 2 ^ g, ∏ b ∈ range (2 ^ n), A (b * 2 ^ g + θ) = h θ

/-- The claim at level l: the multilinear extension of level l has the value t at z. -/
def Claim (g n : ℕ) (A : ℕ → E) (l : ℕ) (z : ℕ → E) (t : E) : Prop :=
  ext (l + g) (lvl g n A l) z = t

/-- The upper half of a vector of 2^(k+1) entries. -/
def up (k : ℕ) (f : ℕ → E) : ℕ → E := fun X => f (X + 2 ^ k)

end Cb.Gp

namespace Cb.Spec
open Blocks Finset Prob Cb.Gp

def rel_iff_zero : Prop :=
  ∀ (E : Type) [Field E] (g n : ℕ) (A h : ℕ → E), Rel g n A h ↔ ∀ θ < 2 ^ g, lvl g n A 0 θ - h θ = 0

def zero_iff_claim0 : Prop :=
  ∀ (E : Type) [Field E] (g n : ℕ) (A h z : ℕ → E),
    ext g (fun θ => lvl g n A 0 θ - h θ) z = 0 ↔ Claim g n A 0 z (ext g h z)

def claim_iff_sum : Prop :=
  ∀ (E : Type) [Field E] (g n : ℕ) (A : ℕ → E) (l : ℕ) (z : ℕ → E) (t : E), l < n →
    (Claim g n A l z t ↔
      ∑ X ∈ range (2 ^ (l + g)),
          eqN (l + g) 0 z X * (lvl g n A (l + 1) X * up (l + g) (lvl g n A (l + 1)) X) = t)

/-- States the defect of the combined claim. -/
def line_defect : Prop :=
  ∀ (E : Type) [Field E] (k : ℕ) (f r : ℕ → E) (c v₀ v₁ : E),
    ext (k + 1) f (consPt c r) - ((1 - c) * v₀ + c * v₁) =
      (1 - c) * (ext k f r - v₀) + c * (ext k (up k f) r - v₁)

/-- States the line step: if one of the two claims on the halves is false, the combined claim holds
for at most one c. -/
def cnt_line_le_one : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (k : ℕ) (f r : ℕ → E) (v₀ v₁ : E),
    (ext k f r ≠ v₀ ∨ ext k (up k f) r ≠ v₁) →
    cnt (fun c : E => ext (k + 1) f (consPt c r) = (1 - c) * v₀ + c * v₁) ≤ 1

/-- States: the combined claim on the halves of level l + 1 is the claim at level l + 1. -/
def line_claim : Prop :=
  ∀ (E : Type) [Field E] (g n : ℕ) (A : ℕ → E) (l : ℕ) (r : ℕ → E) (c t : E),
    Claim g n A (l + 1) (consPt c r) t ↔ ext (l + g + 1) (lvl g n A (l + 1)) (consPt c r) = t

def claim_top : Prop :=
  ∀ (E : Type) [Field E] (g n : ℕ) (A z : ℕ → E) (t : E), Claim g n A n z t ↔ ext (n + g) A z = t

end Cb.Spec
