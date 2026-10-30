-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TestToks.lean: the written list of the head's token sumchecks against the written list
of the plan's places.

Cb/Pv/Head/Sizes.lean lists, for two example configurations, each sumcheck of the head with its
slots and sizes, from a print of the verifier's own planner. Cb/Pv/Head/Toks.lean computes the
slots of the three token sumchecks from the slot of the first row product. The tests compare the
two: slots, numbers of variables, scalars in a round, end values, the scalar that rides in the
first message, and the errors against the rule by which that file states the plan's bounds.

What is not claimed: no theorem is stated. No test here calls a routine of the verifier.


-/
import Cb.Pv.Head.Toks
import Cb.Pv.Head.Sizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok

/-- What is compared of a kind. -/
def seenOf (k : TokKind) : ℕ × ℕ × ℕ × List ℕ × ℕ × ℕ :=
  (k.sCl, k.first, k.sEnd, List.replicate k.vars 2, k.shown, k.sCl + k.slots)

/-- The same of a place in the plan. -/
def seenAt (x : PscAt) : ℕ × ℕ × ℕ × List ℕ × ℕ × ℕ :=
  (x.slot, x.slotSum, x.slotEnd, x.sent, x.values, x.slotEnd + x.values)

#guard sizesTok.map seenOf ==
  ((atTV.zip (atTN.zip atTH)).flatMap fun x => [x.1, x.2.1, x.2.2]).map seenAt
#guard (atTV ++ atTN ++ atTH).all fun x => x.riders == 1 && x.inY == 2 && !x.line
#guard (headSizes.zip atTV).all fun x => x.1.products == (kindTV x.1.lt 0).np &&
  x.1.rowValues == (kindTV x.1.lt 0).shown && x.2.sent.length == x.1.lt
#guard (headSizes.zip atTH).all fun x => x.2.sent.length == x.1.lt + x.1.lPd
#guard sizesTok.map (·.rounds.map (·.2.1)) ==
  ((atTV.zip (atTN.zip atTH)).flatMap fun x => [x.1, x.2.1, x.2.2]).map fun x =>
    (x.riders + 1) :: (x.sent ++ [x.inY, x.values])
#guard sizesTok.map (·.errs) ==
  ((atTV.zip (atTN.zip atTH)).flatMap fun x => [x.1, x.2.1, x.2.2]).map fun x =>
    1 :: ((x.sent ++ [x.inY]) ++ [0])
#guard sizesBat == (headSizes.take 1).flatMap fun x => [x.sums, x.products]

end Cb.Pv.Head.Tok
