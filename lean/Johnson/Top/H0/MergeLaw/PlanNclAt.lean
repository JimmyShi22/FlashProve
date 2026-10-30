-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/PlanNclAt.lean: A FIFTH EQUATION ON THE PLANNER's NUMBERS, beside the four
of Johnson/Top/H0/MergeLaw/PlanNumsAt.lean: how many claims on the committed table the planner's
link number m states, as `FillP1.d1At Z` (Johnson/Top/H0/Fill/D1At.lean) reads it; and the three
tests of that file at the layout's own number of rows. Definitions, statements and proofs.

Main names.
  `nclB Z m n`: a test: the planner has a link number m, and its field NCL is n.
  `ncl_of_test`: then `(FillP1.d1At Z).ncl m = n`.
  `numsB_m0`: `numsB Z m nR` at nR := the layout's number of rows, from its two other tests: the
    test on nR is then true by definition.
Limits. `nclB` is shown true at no Z here: an evaluation at the stored full-size public files is a
loose sheet's, and an evaluation is no proof. Where the planner has no link number m, `d1At` reads 0
and `nclB` rejects at every n, 0 too. Nothing on a verifier's state. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.MergeLaw.PlanNumsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model

/-- A test: the planner has a link number m, and its field NCL is n. -/
def nclB (Z : ProofFile.Pub) (m n : ℕ) : Bool := decide ((Z.p.built.links[m]?).map (·.NCL) = some n)

/-- **Then `d1At Z` reads n claims at link m.** -/
theorem ncl_of_test {Z : ProofFile.Pub} {m n : ℕ} (h : nclB Z m n = true) :
    (FillP1.d1At Z).ncl m = n := by
  show ((Z.p.built.links[m]?).map (·.NCL)).getD 0 = n
  rw [of_decide_eq_true h]
  rfl

/-- The three tests at the layout's own number of rows, from the two that do not read it. -/
theorem numsB_m0 {Z : ProofFile.Pub} {m : ℕ} (h1 : nsB Z m = true)
    (h3 : kColB (VerifiableInference.Desc.K13.whereOf Z).lin Z.p.X.layers.wsLay = true) :
    numsB Z m (FillP1.d1At Z).lay.m0 = true := by
  unfold numsB
  rw [h1, h3]
  show (true && decide (Z.p.X.layers.wsLay.m0 = Z.p.X.layers.wsLay.m0) && true) = true
  simp

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.ncl_of_test
#print axioms VerifiableInference.Desc.First.MergeLaw.numsB_m0
