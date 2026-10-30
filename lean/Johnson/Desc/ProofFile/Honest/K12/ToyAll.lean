-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyAll.lean: a test at one small made-up example: the hypotheses
of `test_accepts_all` and `test_left_all` (WholeAll.lean in this folder) can be met together. `allB`
(AllB.lean in this folder) is a function to Bool: every named clause of the list `allL` holds; at
the example the list has seventeen. The proof of `accepts_of_allB` (AllB.lean) derives the
hypotheses of `test_left_all`, which are those of `test_accepts_all` and one more, from
`allB ... = true`. Here `allB` is proved true at the example, so that theorem's conclusion holds
there. The example is `ToyGroup.one Toy.list₁` (ToyGroup.lean): the job of Toy.lean (`TestJob`,
Test.lean: what a caller supplies for its proximity test) with that file's values. Three stages,
with (k, h) = (3, 0), (1, 1), (0, 0); the first fold's fresh table has come earlier (the field
`mask` of the state on entry is `some`); the test's group is in one tree. Computable definitions,
theorems and evaluations (`#guard`). Made-up numbers only.

In the list: an `At` (ToyAt.lean) holds an example's values: a job, what precedes the test, coins, a
list of challenges, how the prover's rows are read from the first stage's state, and the prover's
input. The block is `proximityTestKind guardedProximityTestParts p` at the job's parameters p. Its decision is `Block.decide`
(Johnson/Desc/Block.lean), here at the job's state on entry (`rec₀`), at the rounds of `testAll`
(Test.lean) without their digests (`noDigest`) and at its lists of opened columns. A group (`Group`,
OnBytes/Iop/Ground.lean) is an entry of the statement in that state; its field `inRun` says that its
proximity test has begun. "Nothing is left untested" is `ChainEnd.NothingLeft`
(Johnson/Desc/ChainEndLaw.lean): a test has begun on every group of the statement, and every sampled
oracle message is in such a group.

  `allB_one`: all seventeen clauses hold at the example: `allB ... = true`, by the kernel's own
    evaluation (`decide +kernel`)
  `accepts_one`: so, by `accepts_of_allB`, the block's decision accepts there, and nothing is left
    untested in the state that it returns
  `coreB_one`: the clauses of `coreB` (AllB.lean) hold at the example too, by the kernel. By
    reading, they are those of `allB` but for "nothing is left untested behind the batching"
  `coreB_more`, `accepts_more`: the clauses of `coreB` hold at `more` of the example, by the kernel,
    and so, by `accepts_of_coreB` (AllB.lean), the block's decision accepts there
  `more`: a definition: an example's values with one more group in the statement of the state on
    entry (`withGroup`, OnBytes/Slice/BlkStLaws.lean). The added group has no member and no row, and
    no test has begun on it
  `At.no`: a definition: the names of the clauses of `allL` that do not hold at an example's values
  `At.yes`: the test's own block, run on all that `testAll` shows: does it accept, and is nothing
    left untested behind it (the library's test). The library's test is `ChainEnd.refuse` at
    `ChainEnd.untestedL` (Johnson/Desc/ChainEnd.lean), at the state that the decision returns
  `At.acc`: a definition: the same decision's acceptance only

What is checked by `#guard`, next to the theorems.
- At the example: `allL` has seventeen clauses; no clause fails; and the block's decision, run,
  accepts, with nothing left untested, as `accepts_one` says.
- Negative tests. Each is an equation on `At.no`: it names exactly the clauses that fail. At `more`
  one further guard evaluates `At.acc` and `At.yes`, and is no such equation.
  The prover's input 1 (this job's state on entry does not read the input, so the prover's tables
  are at another input than the claim's): "RestAsks".
  A position of the first switch out of range (`ToyGroup.far`): "TermAsks".
  The seed's factor 0 (`ToyGroup.flat`): "TermAsks".
  What "BAT" sampled without its element, or with a position too many: no claim is passed after the
  batching, and `allL` is the one false clause that it has for that case, "three stages or more, and
  a claim behind the batching".
  A round of the first fold without its element: "TermAsks", "RestAsks".
  A later round without its elements: "the challenges from the second stage on have the declared
  form".
  One more group, on which no test has begun, in the statement of the state on entry (`more`):
  "nothing is left untested behind the batching" only; and there the block's decision, run, accepts,
  with something left untested.
  The three examples whose first fold sends its own table (`ToyGroup.own Toy.list₁`,
  `ToyTrees.three 0`, `ToyWide.four 0`): "the fresh table has come earlier" and "the plan from the
  second stage on (planFromOk)".
- At these three examples all other clauses hold. They have 2, 3 and 4 trees at the first opening,
  the first fold's own tree among them (tests in ToyGroup.lean, ToyTrees.lean, ToyWide.lean). By
  reading, the clauses that hold give nine of the ten hypotheses of `first_of_shape_own`
  (Johnson/Desc/K12/Honest/Shape/FirstTerm.lean): `Sh.firstB`, the two marks (`stTidyB`,
  `stPlainB`), `claimsB`, the form of what "BAT" sampled, `termB`. The tenth, that `mask` is `none`,
  is that "the fresh table has come earlier" fails. So the hypotheses of that theorem can be met at
  several trees: by Lean's evaluator and by reading; no theorem states it.

By what. `allB_one`, `coreB_one` and `coreB_more` are evaluations by Lean's kernel. `accepts_one` is
`accepts_of_allB` at `allB_one`; `accepts_more` is `accepts_of_coreB` at `coreB_more`.

Limits.
- The theorems are about one small made-up example, at one list of challenges.
- What holds there for nothing: its group stands in one tree; no tree is shorter than the main code
  · the first stage has h = 0: no member has a mask row, and the carried mask table is 0 · no row
  over the base field · exactly three stages: no step from a later stage to a later one that is not
  the last. ("For nothing": what the clauses ask for the cases that the example lacks is vacuous
  there.)
- Every `#guard`, and so every negative test, is an evaluation by Lean's evaluator, outside the
  kernel: it leaves no theorem.
- That something is left untested at `more` of the example is checked by Lean's evaluator only: no
  theorem says it.
- For the other way to leave something untested, a sampled oracle message outside every group whose
  test has begun, no example is given.
- Two names are coarse: by reading, "TermAsks" is the name of thirteen clauses and "RestAsks" of
  sixteen. A negative test does not say which of them failed.
- By reading, eleven of the seventeen names are seen false in no test here: "the place has rounds",
  "the place has oracle messages", `Sh.firstB`, the two marks, `claimsB`, the form of what "BAT"
  sampled, the batching's two numbers, `SwitchPlan`, the sorts of the items. Three of them
  (`Sh.firstB`, `SwitchPlan`, the sorts) are seen false in ToyCame.lean.
- The three examples whose first fold sends its own table are outside what `accepts_of_coreB` and
  `accepts_of_allB` cover.
- A second example, which has most of what this one lacks: ToyCame.lean in this folder.
- `At.yes` and `At.acc` run `Block.decide`, not `Block.step` (Johnson/Desc/Block.lean), and the
  theorems conclude on `Block.decide`. The two checks that `Block.step` makes before the decision,
  on the rounds' form and on the columns' keys, positions and widths, are not evaluated here, nor is
  the block's `planOk`.
- That the block's decision accepts is a statement at one example, and no statement of completeness.
  Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AllB
import Johnson.Desc.ProofFile.Honest.K12.ToyGroup
import Johnson.Desc.ProofFile.Honest.K12.ToyTrees
import Johnson.Desc.ProofFile.Honest.K12.ToyWide

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The names of the clauses of `allL` (AllB.lean) that do not hold at these values. -/
def At.no (A : At) : List String := allNo A.J A.w A.fr A.C A.D (A.lay A.P)

/-- Does the block's `decide` accept `testAll`'s rounds and columns, with nothing left untested? -/
def At.yes (A : At) : Bool :=
  match (proximityTestKind guardedProximityTestParts A.J.p : Block T12 Unit).decide (A.J.rec₀ A.w A.fr)
      ((testAll A.J A.w A.fr A.C A.D).rs.map noDigest) (testAll A.J A.w A.fr A.C A.D).gs with
  | .ok t' => (ChainEnd.refuse (ChainEnd.untestedL t'.st)).isOk
  | .error _ => false

/-- Does the block's `decide` accept `testAll`'s rounds and columns? -/
def At.acc (A : At) : Bool :=
  ((proximityTestKind guardedProximityTestParts A.J.p : Block T12 Unit).decide (A.J.rec₀ A.w A.fr)
    ((testAll A.J A.w A.fr A.C A.D).rs.map noDigest) (testAll A.J A.w A.fr A.C A.D).gs).isOk

/-- The same values with one more group in the statement of the state on entry (`rec₀`): `withGroup`
at the codes 0 and 0. No test has begun on that group. -/
def more (A : At) : At :=
  { A with J := { A.J with rec₀ := fun w fr =>
      { A.J.rec₀ w fr with st := withGroup (A.J.rec₀ w fr).st 0 0 } } }

/-- **All seventeen clauses of `allB` hold at the example of Toy.lean**, by the kernel. -/
theorem allB_one : allB (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w
    (ToyGroup.one Toy.list₁).fr (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D
    ((ToyGroup.one Toy.list₁).lay (ToyGroup.one Toy.list₁).P) = true := by decide +kernel

/-- **So the law's end holds there**: the test's block accepts all that the term shows, and nothing
is left untested. The law is `accepts_of_allB` (AllB.lean); the term is `testAll` (Test.lean). -/
theorem accepts_one : ∃ t', (proximityTestKind guardedProximityTestParts (ToyGroup.one Toy.list₁).J.p : Block T12 Unit).decide
    ((ToyGroup.one Toy.list₁).J.rec₀ (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr)
    ((testAll (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
      (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D).rs.map noDigest)
    (testAll (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w (ToyGroup.one Toy.list₁).fr
      (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D).gs = .ok t' ∧
    ChainEnd.NothingLeft t'.st :=
  accepts_of_allB _ _ _ _ _ _ allB_one

/-- The clauses of `coreB` (AllB.lean) hold there too, by the kernel. -/
theorem coreB_one : coreB (ToyGroup.one Toy.list₁).J (ToyGroup.one Toy.list₁).w
    (ToyGroup.one Toy.list₁).fr (ToyGroup.one Toy.list₁).C (ToyGroup.one Toy.list₁).D
    ((ToyGroup.one Toy.list₁).lay (ToyGroup.one Toy.list₁).P) = true := by decide +kernel

/-- **The clauses of `coreB` hold with one more group in the statement of the state on entry**
(`more`): an empty group, on which no test has begun. That something is left untested there is
checked by Lean's evaluator only (two `#guard` below): no theorem says it. For the other way to
leave something untested, a sampled oracle message outside every group whose test has begun, no
example is given. -/
theorem coreB_more : coreB (more (ToyGroup.one Toy.list₁)).J (more (ToyGroup.one Toy.list₁)).w
    (more (ToyGroup.one Toy.list₁)).fr (more (ToyGroup.one Toy.list₁)).C
    (more (ToyGroup.one Toy.list₁)).D
    ((more (ToyGroup.one Toy.list₁)).lay (more (ToyGroup.one Toy.list₁)).P) = true := by
  decide +kernel

/-- **So the block's decision accepts there**: by the theorem `accepts_of_coreB` (AllB.lean), not by
a run. -/
theorem accepts_more :
    ∃ t', (proximityTestKind guardedProximityTestParts (more (ToyGroup.one Toy.list₁)).J.p : Block T12 Unit).decide
      ((more (ToyGroup.one Toy.list₁)).J.rec₀ (more (ToyGroup.one Toy.list₁)).w
        (more (ToyGroup.one Toy.list₁)).fr)
      ((testAll (more (ToyGroup.one Toy.list₁)).J (more (ToyGroup.one Toy.list₁)).w
        (more (ToyGroup.one Toy.list₁)).fr (more (ToyGroup.one Toy.list₁)).C
        (more (ToyGroup.one Toy.list₁)).D).rs.map noDigest)
      (testAll (more (ToyGroup.one Toy.list₁)).J (more (ToyGroup.one Toy.list₁)).w
        (more (ToyGroup.one Toy.list₁)).fr (more (ToyGroup.one Toy.list₁)).C
        (more (ToyGroup.one Toy.list₁)).D).gs = .ok t' :=
  accepts_of_coreB _ _ _ _ _ _ coreB_more

-- the example once more, by Lean's evaluator
#guard (allL (ToyGroup.one Toy.list₁).J 0 (ToyGroup.one Toy.list₁).fr (ToyGroup.one Toy.list₁).C
  (ToyGroup.one Toy.list₁).D ((ToyGroup.one Toy.list₁).lay (ToyGroup.one Toy.list₁).P)).length == 17
#guard (ToyGroup.one Toy.list₁).no == []
#guard (ToyGroup.one Toy.list₁).yes
-- negative tests: another input; a position out of range; the seed's factor 0
#guard (ToyGroup.one Toy.list₁ 1).no == ["RestAsks"]
#guard (ToyGroup.one (ToyGroup.far Toy.list₁)).no == ["TermAsks"]
#guard (ToyGroup.one (ToyGroup.flat Toy.list₁)).no == ["TermAsks"]
-- what "BAT" (round 0) sampled without its element, or with a position too many: no claim is passed
-- after the batching; a round of the first fold (3), and a later round (8), without its elements
#guard (ToyGroup.one (Toy.list₁.modify 0 fun d => { d with elems := [] })).no ==
  ["three stages or more, and a claim behind the batching"]
#guard (ToyGroup.one (Toy.list₁.modify 0 fun d => { d with poss := [0] })).no ==
  ["three stages or more, and a claim behind the batching"]
#guard (ToyGroup.one (Toy.list₁.modify 3 fun d => { d with elems := [] })).no ==
  ["TermAsks", "RestAsks"]
#guard (ToyGroup.one (Toy.list₁.modify 8 fun d => { d with elems := [] })).no ==
  ["the challenges from the second stage on have the declared form"]
-- one more group, on which no test has begun
#guard (more (ToyGroup.one Toy.list₁)).no == ["nothing is left untested behind the batching"]
-- there the block's decision, run, accepts; something is left untested after it
#guard (more (ToyGroup.one Toy.list₁)).acc && !(more (ToyGroup.one Toy.list₁)).yes
-- outside what the theorems of AllB.lean cover: the first fold sends its own table
#guard [ToyGroup.own Toy.list₁, ToyTrees.three 0, ToyWide.four 0].all fun A =>
  A.no == ["the fresh table has come earlier", "the plan from the second stage on (planFromOk)"]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.allB_one
#print axioms ProofFile.Honest.K12.accepts_one
#print axioms ProofFile.Honest.K12.coreB_one
#print axioms ProofFile.Honest.K12.coreB_more
#print axioms ProofFile.Honest.K12.accepts_more
#print axioms ProofFile.Honest.K12.At.no
#print axioms ProofFile.Honest.K12.At.yes
#print axioms ProofFile.Honest.K12.At.acc
#print axioms ProofFile.Honest.K12.more
