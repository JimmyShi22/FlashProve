-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/RngAlg.lean: an approximate range proof (a protocol for the claim that every entry of a
matrix over a ring is the image of an integer of bounded absolute value; for the bound and the error
of the draw see `Spec.cnt_allPass_mul_le` below): its plain mathematics, without any protocol.

In this library's words: the approximate range check, one cell (an integer) for each element.

Definitions and statements; the proofs are in Cb/Gen/RngAlgProofs.lean.

The test: a matrix Y over a ring F of characteristic p, rows R, columns C. The verifier draws |U|
vectors of coefficients in {-1, 0, 1} (0 with probability 1/2, each sign with probability 1/4:
`Prob.Coef`, two uniform bits); the prover writes every entry of every combination, shifted by D,
in two digits at the radix q, the low one below q and the high one below H, where q H = 2 D.

Main names, each under the hypotheses of its statement:
  `Spec.cnt_allPass_mul_le` (soundness): if some entry of Y is not the image of an integer of
    absolute value below 2 D, all |U| combinations are in the window [-D, D) for at most the
    fraction 2^(-|U|) of the challenges. `Spec.short_of_pass_two` is the step for one column: see
    its docstring.
  `Spec.pass_of_digits` (soundness): digits in their tables that satisfy the rows
    (combination = l + q h - D) put the combination in the window (error 0).
  `Spec.digits_ok` (honest side): outside the window event the digits of the integer combination
    are in their tables and satisfy the rows.
  `Spec.pr_event_le` (honest side): an upper bound on the probability of the window event.
    `Spec.event_empty`: a case in which the event is empty.
  `Spec.short_iff_valMinAbs`, `Spec.rep_unique`: see their docstrings; both ask 2 b ≤ p + 1. With
    b = 2 D this is where the condition 4 D < p of the written protocol enters; the counts do not
    need it.

Limits: this file says nothing on oracles, codes or decoding, and nothing on the lookup that checks
the digits.

The test is the field's approximate range proof with ternary coefficients, as the protocol of this
protocol's technical report, which follows the texts named in lean/CREDITS.md, uses it; the counts
are those of Prob/Window.lean. (Alg/Range.lean
has the variant with three cells an element.)

Terms: lean/GLOSSARY.md.
-/
import Prob.Window
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.CharP.Basic

set_option autoImplicit false

namespace Cb.Rng
open Prob Finset
open scoped ENNReal

variable {F : Type} [CommRing F]

/-- x is the image of an integer of absolute value below b. -/
def Short (b : ℤ) (x : F) : Prop := ∃ a : ℤ, |a| < b ∧ x = (a : F)

/-- x is the image of an integer of the window [-D, D). -/
def InWin (D : ℤ) (x : F) : Prop := ∃ a : ℤ, -D ≤ a ∧ a < D ∧ x = (a : F)

/-- x is the image of a natural number below q: an entry of the table [0, q). -/
def InTab (q : ℕ) (x : F) : Prop := ∃ a : ℕ, a < q ∧ x = (a : F)

/-- The combination of the columns of Y with the coefficients cf, row r. -/
def combF {R C : Type} [Fintype C] (Y : R → C → F) (cf : C → ℤ) (r : R) : F :=
  ∑ c, (cf c : F) * Y r c

/-- A vector of coefficients passes: every entry of the combination is in the window. -/
def Pass {R C : Type} [Fintype C] (D : ℤ) (Y : R → C → F) (cf : C → ℤ) : Prop :=
  ∀ r, InWin D (combF Y cf r)

/-- The window event for an integer matrix: an entry of some combination leaves the window. -/
def Event {R C U : Type} [Fintype C] (D : ℤ) (Yz : R → C → ℤ) (Λ : U → C → Coef) : Prop :=
  ∃ x : R × U, ¬ (-D ≤ comb (Yz x.1) (Λ x.2) ∧ comb (Yz x.1) (Λ x.2) < D)

/-- The honest digits `lo`, `hi` of an integer z of the window, shifted by D, at the radix q. -/
def lo (D : ℤ) (q : ℕ) (z : ℤ) : ℕ := (z + D).toNat % q
def hi (D : ℤ) (q : ℕ) (z : ℤ) : ℕ := (z + D).toNat / q

end Cb.Rng

namespace Cb.Spec
open Prob Finset Cb.Rng
open scoped ENNReal

/-- States: if a combination passes with 0 at the column c₀ and also with +1 or -1 there, the other
coefficients being the same, every entry of the column is `Short (2 * D)`. -/
def short_of_pass_two : Prop :=
  ∀ (F : Type) [CommRing F] (R C : Type) [Fintype C] [DecidableEq C] (D : ℤ) (Y : R → C → F)
      (cf : C → ℤ) (c₀ : C) (e : ℤ),
    e = 1 ∨ e = -1 → Pass D Y (Function.update cf c₀ 0) →
    Pass D Y (Function.update cf c₀ e) → ∀ r, Short (2 * D) (Y r c₀)

/-- States soundness of the draw: if some entry is not `Short (2 * D)`, all combinations pass for at
most the fraction 2^(-|U|) of the challenges. -/
def cnt_allPass_mul_le : Prop :=
  ∀ (F : Type) [CommRing F] (R C U : Type) [Fintype C] [DecidableEq C] [Fintype U] [DecidableEq U]
      (D : ℤ) (Y : R → C → F),
    (¬ ∀ r c, Short (2 * D) (Y r c)) →
    cnt (fun Λ : U → C → Coef => ∀ u, Pass D Y fun c => (Λ u c).val) * 2 ^ Fintype.card U ≤
      Fintype.card (U → C → Coef)

/-- States soundness of the digits, error 0: if q H = 2 D, digits in their tables [0, q), [0, H)
that satisfy the rows, combination = l + q h - D, put the combination in the window. -/
def pass_of_digits : Prop :=
  ∀ (F : Type) [CommRing F] (R C : Type) [Fintype C] (D : ℤ) (q H : ℕ) (Y : R → C → F)
      (cf : C → ℤ) (l h : R → F),
    (q : ℤ) * H = 2 * D → (∀ r, InTab q (l r)) → (∀ r, InTab H (h r)) →
    (∀ r, combF Y cf r = l r + (q : F) * h r - (D : F)) → Pass D Y cf

/-- States of the honest digits: if 0 < q and q H = 2 D, then for an integer combination in the
window they are in their tables and satisfy the row. -/
def digits_ok : Prop :=
  ∀ (F : Type) [CommRing F] (C : Type) [Fintype C] (D : ℤ) (q H : ℕ) (y : C → ℤ) (g : C → Coef), 0 <
      q →
    (q : ℤ) * H = 2 * D → -D ≤ comb y g → comb y g < D →
    lo D q (comb y g) < q ∧
    hi D q (comb y g) < H ∧
    ∑ c, (((g c).val : ℤ) : F) * ((y c : ℤ) : F) =
      ((lo D q (comb y g) : ℕ) : F) + (q : F) * ((hi D q (comb y g) : ℕ) : F) - (D : F)

/-- States, if the entries have absolute value below B, B ≥ 2, 0 ≤ D and C is not empty, an upper
bound on the probability of the window event. -/
def pr_event_le : Prop :=
  ∀ (R C U : Type) [Fintype R] [Fintype C] [DecidableEq C] [Nonempty C] [Fintype U] [DecidableEq U]
      (B D : ℤ) (Yz : R → C → ℤ),
    2 ≤ B → 0 ≤ D → (∀ r c, |Yz r c| < B) →
    pr (unif (U → C → Coef)) {Λ | Event D Yz Λ} ≤
      Fintype.card (R × U) *
        ENNReal.ofReal (2 * Real.exp (-((D : ℝ) ^ 2 / (Fintype.card C * ((B - 1 : ℤ) : ℝ) ^ 2))))

/-- States: if every entry has absolute value below 1 (the case B = 1, which `pr_event_le` leaves
out: the matrix is 0) and 0 < D, the event is empty. -/
def event_empty : Prop :=
  ∀ (R C U : Type) [Fintype C] (D : ℤ) (Yz : R → C → ℤ),
    0 < D → (∀ r c, |Yz r c| < 1) → ∀ Λ : U → C → Coef, ¬ Event D Yz Λ

/-- States: if F has characteristic p and 2 b ≤ p + 1, the integer of absolute value below b behind
an element is unique. -/
def rep_unique : Prop :=
  ∀ (F : Type) [CommRing F] (p : ℕ) [CharP F p] (b a a' : ℤ),
    2 * b ≤ p + 1 → |a| < b → |a'| < b → (a : F) = (a' : F) → a = a'

/-- States, in ZMod p with p ≠ 0 and 2 b ≤ p + 1: `Short b x` means that the representative of x of
least absolute value has absolute value below b. -/
def short_iff_valMinAbs : Prop :=
  ∀ (p : ℕ) [NeZero p] (b : ℤ), 2 * b ≤ p + 1 → ∀ x : ZMod p, Short b x ↔ |x.valMinAbs| < b

end Cb.Spec
