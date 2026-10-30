-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadLaid.lean: THE OUTPUT HEAD'S OWN ROUNDS: MORE TESTS ON THE PLAN: on numbers
that the text's letters do not hold, and on which its meaning and its laws lean. With code, on
public numbers alone. Definitions; no theorem. WHO ASKS IT: the block as a lot seats it
(Stored/HeadSeatAt.lean: laidOk, in seatedOf's test on the plan); the kind's own Par.ok does not.
WHY. The text takes limb l of the stream's feature j at feature l d + j of its matrix, five limbs,
from feature 0 on; a long read's entry is a block of S2 = 2^(la - lt) features. The program lays the
stream by the layers' layout's numbers (first feature, limbs, layers, features of a limb) and lets
four limbs by. Where these part, a proof that the kind accepts speaks of other cells than the text
says. None of planOk's tests reads these numbers. Three tests more are on letters that
the text does hold: "whole": the vocabulary fills its blocks (JV = V: no padding entry); "clip" and
"mean": C and theta are below 2^40 (the five digits of the numbers that hold them; the library's own
condition on a policy): planOk says yes at 2^40.

-/
import Johnson.Desc.Kinds.HeadOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open Norm (lt ls d lPd T S2)
variable [Sizes] [Policy]

/-- Numbers of the plan beside the sizes. -/
structure Laid where
  /-- the logarithm of the number of rows of a block of a long read -/
  la : Nat
  /-- the plan's own logarithm of d with padding -/
  padLog : Nat
  /-- the limbs of a value of the stream: as the head's shape says; as the stream's tensor says -/
  limbs : Nat
  laidLimbs : Nat
  /-- the first feature of the stream's tensor in its matrix -/
  off : Nat
  /-- from a limb's feature to the next limb's -/
  step : Nat
  /-- the entries of a read of the stream's matrix -/
  room : Nat
  deriving DecidableEq, Repr

/-- The tests, each under its name. The last is narrower than the kind's own test on the plan, which
lets sh = 7 by. "block's logarithm" is true by definition at a seat whose sizes take ls as la - lt
(Stored/HeadSeatAt.lean's does): there sixteen of the seventeen can say no. -/
def Laid.tests (x : Laid) : List (String × Bool) :=
  [("features", decide (1 ≤ d)), ("point", decide (1 ≤ lt)), ("rows", decide (lt ≤ x.la)),
   ("block's logarithm", ls == x.la - lt), ("block", decide (ls ≤ lPd)), ("pad", x.padLog == lPd),
   ("limbs", x.limbs == 5), ("the tensor's limbs", x.laidLimbs == 5),
   ("index", decide (lt + lPd ≤ 63)), ("rows' index", decide (x.la ≤ 63)),
   ("origin", x.off == 0), ("step", x.step == d), ("stream", decide (5 * d / S2 ≤ x.room)),
   ("whole", JV == V), ("clip", decide (C < 2 ^ 40)), ("mean", decide (theta < 2 ^ 40)),
   ("shift", sh == 8)]

def Laid.ok (x : Laid) : Bool := x.tests.all (·.2)

/-- The names of the tests that say no. -/
def Laid.fails (x : Laid) : List String := (x.tests.filter (!·.2)).map (·.1)

end VerifiableInference.Desc.Kinds.Head
