-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/FlatTests.lean: the five tests that the flat hearing functions make of a round's
weight and form, under names of their own. Definitions alone.

Why. OnBytes/K/Kc/Flat.lean is plain text of its own but for two lines: Fl.pscRound asked
"w.fits && Model.weightHeld w", and Fl.roundIn asked "form.weight z degree". Through them every
caller of a masked sumcheck reached five tests of `verify-on-bytes`. Here each stands under a name
of its own. THE TEXT IS NOT NEW: all seven definitions are those of `verify-on-bytes` token for
token, names apart:
  fitsT w        for  Psc.Weight.fits w        the sizes of a weight fit
  heldT w        for  Model.weightHeld w       the coefficient that is not sent can be solved for,
                                               and the sum of moment[i] * psi[i] is 1
  admitsT f n    for  RoundForm.degreeOK f n   the form admits the degree
  atPointT f     for  RoundForm.equality f     the form sums with the weights 1 - z and z
  weightT f z n  for  RoundForm.weight f z n   the weight of a round of that form
and two helpers that these need: dotT (for Psc.dot) and valuesT (for Model.roundValues).
That each agrees with that of `verify-on-bytes`: OnBytes/K/Kc/FlatTestsSame.lean (at all arguments)
and OnBytes/K/Kc/FlatTestsRfl.lean (by definition).

What this text still names of the library, all of it: the record OnBytes.Psc.Weight with its
fields (d, moment, psi, fixed, fixedInv); its two makers OnBytes.Psc.Weight.equality and
OnBytes.Psc.Weight.plain, each of which returns a record outright; the datatype
OnBytes.Model.RoundForm with its five forms; the field's element type E and its arithmetic (addE,
mulE, zeroE, oneE); and three tests of equality (==): of Nat, of RoundForm and of E, the last two by
way of the decidable equality that Lean derives for these types. No other test, no routine, no
context. All seven definitions are plain: none is partial, none has a twin that runs in its place.

Limits. THIS TAKES FIVE NAMES OUT OF THE CONE, NOT FIVE TESTS OUT OF THE VERIFIER: the text here is
that of `verify-on-bytes`, copied (names apart); whatever is right or wrong in its five tests is
carried over to the letter, and a walk by names, which cannot see copied text, then finds none of
the five. It has to be so: each definition's shape follows the one in `verify-on-bytes` (see the
comments at admitsT, atPointT and valuesT), and that is what makes the agreement hold by definition.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Iop.Psc
import OnBytes.Model.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc

/-- The sizes of a weight fit: at least two coefficients; one moment for each; psi no longer; the
coefficient that is not sent is one of them. -/
def fitsT (w : OnBytes.Psc.Weight) : Bool :=
  decide (2 ≤ w.d) && w.moment.length == w.d && decide (w.psi.length ≤ w.d) &&
    decide (w.fixed < w.d)

/-- The sum of the products of the members of two lists, as far as the shorter goes. -/
def dotT (a b : List E) : E :=
  (a.zip b).foldl (fun r p => addE r (mulE p.1 p.2)) zeroE

/-- The moment of the coefficient that is not sent times fixedInv is 1, and the sum of
moment[i] * psi[i] is 1. -/
def heldT (w : OnBytes.Psc.Weight) : Bool :=
  mulE (w.moment.getD w.fixed zeroE) w.fixedInv == oneE && dotT w.moment w.psi == oneE

/-- The form admits the degree: 1 to 64 where the caller gives it (nodes, eq); any where the form
fixes it. Written as a formula in the form's test of equality, as in `verify-on-bytes`, not by
cases: so it agrees with its test by definition also at a form that is a letter (FlatTestsRfl.lean).
A text by cases does not, and the proof at OnBytes/K/Kc/Proved.lean:93 fails over it. -/
def admitsT (form : OnBytes.Model.RoundForm) (degree : Nat) : Bool :=
  !(form == .nodes || form == .eq) || (decide (1 ≤ degree) && decide (degree ≤ 64))

/-- The form sums with the weights 1 - z and z. The cases stand as in the test of `verify-on-bytes`:
two by name, then "all others". A text that names all five forms agrees with that test at each
form but, by Lean's own word, not by definition at a form that is a letter; in this shape it does
(FlatTestsRfl.lean). Why that is so has not been looked into. -/
def atPointT : OnBytes.Model.RoundForm → Bool
  | .eq2 => true
  | .eq => true
  | _ => false

/-- The number of scalars that a round of the form sends. The cases stand as in `verify-on-bytes`,
in its order: of this one the same was seen. -/
def valuesT (form : OnBytes.Model.RoundForm) (degree : Nat := 0) : Nat :=
  match form with
  | .sum3 => 3
  | .nodes => degree
  | .eq => degree
  | .eq2 => 2
  | .sum2 => 2

/-- The weight of a round of the form; none if the form does not admit the degree. z is read for eq2
and eq, degree for nodes and eq; both have the defaults that they have in `verify-on-bytes`. -/
def weightT (form : OnBytes.Model.RoundForm) (z : E := zeroE) (degree : Nat := 0) :
    Option OnBytes.Psc.Weight :=
  if admitsT form degree then
    let d := valuesT form degree + 1
    some (if atPointT form then OnBytes.Psc.Weight.equality z d else OnBytes.Psc.Weight.plain d)
  else none

end OnBytes.K.Kc
