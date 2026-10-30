-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestPlanner.lean: plans that the verdict must refuse.

Each case takes numbers that hold and makes them worse by one step: a position fewer, a slack one
step smaller, a combination fewer. The C++ tree has builds with the same three faults planted
(blocks/numbers/blocks.h). Further cases: a group with more row variables for mask rows than for
main rows, a stage priced at two distances, and a round whose word on how it was priced contradicts
it. The setting and the group are those of an entry under
blocks/frame/examples/record.f2.txt. Each test is checked when the file compiles.
The file is no part of the program.
-/
import OnBytes.Params.Derive
import OnBytes.Params.TestExamples

namespace OnBytes.Params.TestPlanner

/-- The setting of the example, and the stages of the test on an entry's two folded rows. -/
def example1 : Option (Setting × List StageSize) :=
  (readLines (TestFile.fileOf TestExamples.record)).toOption.bind fun x =>
    (entrySized x.1).toOption.map fun y => (settingOf x.1, y.1.linked.stages)

/-- What the three parts of the verdict say of a routine's plan in the committer's scope. -/
def verdict (s : Setting) (x : Planning Unit) : Option (Bool × Bool × Bool) :=
  (finish s .once x).toOption.map fun p => (p.roundsHold, p.wordsFit, p.oneDistance)

/-- The round that draws t positions on a group's rows, as the last step of a test plans it. -/
def draw (s : Setting) (g : GroupSize) (t : Nat) : Planning Unit :=
  close "BASE" .query (Bound.pow (analysis s g).mainAt.agree t)
    { poss := t, logN := g.main.logN, group := pricedOf g, priced := .asSaid }

-- the numbers of the example: the integer 182 at the first stage, 40 positions at the last
#guard example1.any fun x => (x.2.head?.map (·.g.m)) == some 182 &&
  (x.2.getLast?.map (·.t)) == some 40
-- the last stage's list holds with its 40 positions and not with 39
#guard (example1.bind fun x => x.2.getLast?.bind fun st => verdict x.1 (draw x.1 st.g st.t)) ==
  some (true, true, true)
#guard (example1.bind fun x => x.2.getLast?.bind fun st =>
    verdict x.1 (draw x.1 st.g (st.t - 1))) == some (false, true, true)
-- the first stage's fold holds at the integer 182 of its distance and not at 183
#guard (example1.bind fun x => x.2.head?.bind fun st => verdict x.1 (planFold st.g 0)) ==
  some (true, true, true)
#guard (example1.bind fun x => x.2.head?.bind fun st =>
    verdict x.1 (planFold { st.g with m := st.g.m + 1 } 0)) == some (false, true, true)
-- a group with more row variables for mask rows than for main rows: no plan is made
#guard example1.any fun x => x.2.head?.any fun st =>
  (verdict x.1 (planFold { st.g with k := 1, h := 2 } 0)).isNone &&
  (verdict x.1 (planLoc { st.g with k := 1, h := 2 } *> pure ())).isNone &&
  (verdict x.1 (planFold { st.g with k := 2, h := 2 } 0)).isSome
-- the matrix of a smallness test holds with 128 combinations and not with 127
#guard (example1.bind fun x => verdict x.1 (planRng 100)) == some (true, true, true)
#guard (example1.bind fun x => verdict x.1
    (close "RNG" .small (Bound.exact (Binary.twoTo (-127)))
      { trits := 12700, combinations := 127, priced := .asSaid })) == some (false, true, true)
-- two folds on the same two codes at two distances
#guard (example1.bind fun x => x.2.head?.bind fun st => verdict x.1 do
    planFold st.g 0
    planFold { st.g with m := 100 } 0) == some (true, true, false)
-- a batching of no rows: it is priced from what is said beside it, and nothing is said
#guard (example1.bind fun x => verdict x.1 (planBatSigma 0)) == some (true, false, true)
#guard (example1.bind fun x => verdict x.1 (planBatSigma 1)) == some (true, true, true)
-- a plan that ends in the middle of a prover's message; a root in a round without a verifier's
-- message
#guard (example1.bind fun x => verdict x.1 (planScalars 1)) == none
#guard (example1.bind fun x => verdict x.1 do
    planRoots 1
    closeNone "LAST") == none

end OnBytes.Params.TestPlanner
