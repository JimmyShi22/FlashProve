-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestRangesGate.lean: tests of OnBytes/Plan/RangesGate.lean on the example
prover/examples/target_small_f2_roomy in another form. They run when this file compiles.

The C++ verifier admits that form's public files, so no condition is missed. The other tests are at
the edge of conditions 1 and 3 of RangesGate.lean, as in the C++ programs' own test of these
conditions (blocks/frame/tests/hiding_conditions_test.cpp). Condition 2 has no test here.
 1. One random entry less in the main code, or in the mask code, of any one stage of the proof's
    proximity test: a condition is missed.
 2. The oracle message of the multiplicities has the least number of mask rows that holds what the
    lookups take. With one row less a condition is missed.
missedInTheRanges also says yes if the chain's rounds cannot be planned. So each altered key is made
as a wrong sizing would have made it, with sizes and codes changed alike, and each test asks as
well that the rounds of the altered key can be planned.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.RangesGate
import OnBytes.Plan.TestKeyOneTime

namespace OnBytes.Plan.TestRangesGate

open OnBytes.Params

/-- The example's key with another number of mask rows in the oracle message of the
multiplicities. -/
def withMaskRows (z : KeySized) (rows : Nat) : KeySized :=
  { z with ranges := { z.ranges with x := { z.ranges.x with
      message := { z.ranges.x.message with
        shape := { z.ranges.x.message.shape with maskRows := rows } } } } }

/-- One random entry less. -/
def less (c : Code) : Code := { c with r := c.r - 1 }

/-- A group with one random entry less in its main code (main true) or in its mask code. -/
def lessIn (main : Bool) (g : GroupSize) : GroupSize :=
  if main then { g with main := { g.main with r := g.main.r - 1 } }
  else { g with mask := { g.mask with r := g.mask.r - 1 } }

/-- The example's key with one random entry less in the main code (main true) or the mask code of
stage number i of the proof's proximity test, in the list of codes and in the sizes alike. -/
def lessAt (main : Bool) (i : Nat) (z : KeySized) : KeySized :=
  let st := z.ranges.x.stages.getD i default
  { z with
    codes :=
      if main then { z.codes with base := z.codes.base.modify st.code less }
      else { z.codes with mask := z.codes.mask.modify st.maskCode less }
    ranges := { z.ranges with test := { z.ranges.test with
      stages := ((List.range z.ranges.test.stages.length).zip z.ranges.test.stages).map fun s =>
        if s.1 != i then s.2 else { s.2 with g := lessIn main s.2.g } } } }

/-- The rounds of a key's first chain can be planned. -/
def planned (z : KeySized) : Bool := (finish z.set .once (oneTimeRounds z)).toOption.isSome

/-- The rounds can be planned, and a condition is missed. -/
def missedThoughPlanned (z : KeySized) : Bool := planned z && missedInTheRanges z

#guard TestKeyOneTime.sized.any fun z => planned z && !missedInTheRanges z
-- the proof's test has stages under main codes of their own
#guard TestKeyOneTime.sized.any fun z =>
  let cs := z.ranges.x.stages.map (·.code)
  cs.length == 4 && cs.eraseDups.length == cs.length
#guard TestKeyOneTime.sized.any fun z =>
  (List.range z.ranges.x.stages.length).all fun i => missedThoughPlanned (lessAt true i z)
#guard TestKeyOneTime.sized.any fun z =>
  (List.range z.ranges.x.stages.length).all fun i => missedThoughPlanned (lessAt false i z)

/-- The least number of mask rows with room for what the lookups take of them. -/
def leastRows (z : KeySized) : Nat :=
  let taken := Wf.ownMasks z.ranges.x z.ranges.matrix
  let inARow := (codeAt z.codes.mask z.ranges.x.message.shape.maskCode).ell - z.set.samples
  (taken + 1 + inARow) / (inARow + 1)

#guard TestKeyOneTime.sized.any fun z => z.ranges.x.message.shape.maskRows == leastRows z
#guard TestKeyOneTime.sized.any fun z => missedThoughPlanned (withMaskRows z (leastRows z - 1))
-- as many scalars are sent as mask entries are used
#guard TestKeyOneTime.sized.any fun z => (lookupScalars z).toOption ==
  some (Wf.ownMasks z.ranges.x z.ranges.matrix + Wf.indexMasks z.ranges.x z.ranges.matrix)

end OnBytes.Plan.TestRangesGate
