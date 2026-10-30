-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/FlatTestsRfl.lean: the five tests of OnBytes/K/Kc/FlatTests.lean unfold to what the
tests of the program `verify-on-bytes` unfold to: each agreement holds by definition ("rfl"), with
every argument a letter. Theorems.

Why it matters. A proof of another file that unfolds Fl.pscRound or Fl.roundIn and then hands the
test's hypothesis on by "exact" or by unification (as a fact on w.fits, Model.weightHeld w or
form.weight z degree) goes through, because Lean unfolds both sides to one term. A proof that
rewrites with a lemma whose left side names a test of `verify-on-bytes` does not: it wants fitsT_eq,
heldT_eq or weightT_eq (OnBytes/K/Kc/FlatTestsSame.lean) in front.

Limits. A file of its own, so that a failure here would not hold up FlatTestsSame.lean, whose proofs
do not lean on this.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.FlatTestsSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc
open OnBytes.Model (RoundForm)

theorem fitsT_rfl : fitsT = OnBytes.Psc.Weight.fits := rfl

theorem heldT_rfl : heldT = Model.weightHeld := rfl

theorem admitsT_rfl : admitsT = RoundForm.degreeOK := rfl

theorem atPointT_rfl (form : RoundForm) : atPointT form = form.equality := rfl

theorem valuesT_rfl (form : RoundForm) (degree : Nat) :
    valuesT form degree = Model.roundValues form degree := rfl

theorem weightT_rfl (form : RoundForm) (z : E) (degree : Nat) :
    weightT form z degree = form.weight z degree := rfl

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.weightT_rfl
