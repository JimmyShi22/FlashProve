-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TermLen.lean: how many rounds `testAll` (Test.lean in this folder)
lists for a proximity test: `termLen`, a number computed from the list of stages only
(`length_test`). At three places this is proved to be the number of rounds that the test's block
declares (`count_toy`, `count_came`, `count_KR`): the two numbers are compared by an evaluation in
Lean's kernel. The equation of these three theorems is the field `count` of `K12At` (SaysYesK12.lean
in this folder); that of `termLen_KR` has the form of the field `count` of `PlanPlays`
(PlaysK12.lean). `length_stages` and `length_test` are general: they have no hypothesis.
Definitions, statements and proofs.

In the list: a stage is a `Fmt.M1.Stage` (Fmt/M1Types.lean); its h and g are those of `sgOf`
(Johnson/Desc/K12/Law/ChainOf.lean), where g is k - h in the natural numbers: h + g is k where h is
at most k. A place is a `P12` (Johnson/Desc/K12/Frame.lean): the numbers of a place of a proximity
test, among them the list of stages `nums.stages`. The block at a place p is `proximityTestKind guardedProximityTestParts p`
(Frame.lean and JoinGuarded.lean in Johnson/Desc/K12/); the rounds that it declares are its field
`rounds`. A job is a `TestJob` (Test.lean): what a caller supplies for its test; `J.p` is its place.
A front is a `Front` (Johnson/Desc/ProofFile/Honest/Sum.lean): what precedes the test. The rounds
that `testAll` and `stagesAll` list are the field `rs` of their value (`BOut`,
Johnson/Prover/Link/BodyAll.lean).

  `length_test`: `testAll J w fr C D` lists `termLen J.p.nums.stages` rounds, at every job, input,
    front, coins and challenges
  `count_toy`, `count_came`: at the job `Toy.J` (Toy.lean in this folder) and at the job of
    `ToyCame.came 0` (ToyCame.lean), at every input, front, coins and challenges: `testAll` lists
    as many rounds as the block at the job's place declares
  `count_KR`: the same at every job J with `J.p = piKRFull`. `piKRFull`
    (Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean) is the place of the key file's test on the
    ranges at the full size, written out as a closed term. `count_KRs` (Sim/ExactAtKR.lean) is
    another statement: on `laidOf`, `firstLen` and `restLen` at that place
  `termLen_KR`: `termLen` at the stages of `piKRFull` is the number of rounds that the block at
    `piKRFull` declares
  `length_stages`: `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) from a stage cur on, with the
    later stages rest, lists `lenFrom cur rest` rounds, at all its other arguments
  `lenFrom cur rest`: a definition: the number of rounds of the stages from cur on: 2 where rest is
    empty; else h + g + 3 at cur, plus the number from the next stage on
  `termLen`: a definition: the number of rounds of the whole test: 0 at the empty list of stages;
    else 1, for the round "BAT", plus `lenFrom` from the first stage on

By what. `length_stages` goes by recursion on the later stages: the last stage by unfolding; at
every other stage `length_aFold` (Johnson/Desc/K12/Honest/Causal.lean: a fold has 1 + (h + g)
rounds), the switch's two rounds, and `omega`. `length_test` unfolds `testAll` and calls
`length_stages`. `count_toy` and `count_came` are `length_test` followed by the numbers' equation,
which is proved by `decide +kernel`; so is `termLen_KR`. `count_KR` rewrites by `length_test` and by
its hypothesis and calls `termLen_KR`.

Limits. The statements are on numbers of rounds only. That `termLen` is the number of rounds that
the block declares is proved at these three places only: no general statement of it is in this file.
The places of Toy.lean and ToyCame.lean are small and made up. No job at `piKRFull` is defined in
this file. The limits of PlaceKeyRangesFull.lean hold here as well. Nothing on a decision, on
completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.ToyCame
import Johnson.Desc.K12.Law.PlaceKeyRangesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2K.Member (piKRFull)

variable {W X : Type}

/-- The number of rounds of the stages from a stage on: 2 for the last stage; h + g + 3 for every
other stage, with the h and g of `sgOf`. -/
def lenFrom : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ
  | _, [] => 2
  | cur, next :: rest => (sgOf cur).h + (sgOf cur).g + 3 + lenFrom next rest

/-- The number of rounds of the whole test: 0 where there is no stage; else the round "BAT" and the
rounds of the stages. -/
def termLen : List Fmt.M1.Stage → ℕ
  | [] => 0
  | s :: rest => 1 + lenFrom s rest

theorem length_stages (p : P12) (K : BCoins) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn), (stagesAll p K rest j cur l o t P trees D).rs.length = lenFrom cur rest
  | [], _, _, _, _, _, _, _, _ => rfl
  | next :: rest, j, cur, l, o, t, P, trees, D => by
    simp only [stagesAll, List.length_append, length_aFold,
      length_stages p K rest (j + 1) next]
    show 1 + ((sgOf cur).h + (sgOf cur).g) + 2 + lenFrom next rest =
      (sgOf cur).h + (sgOf cur).g + 3 + lenFrom next rest
    omega

/-- **`testAll` lists `termLen` rounds**, at every job, input, front, coins and challenges. -/
theorem length_test (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll J w fr C D).rs.length = termLen J.p.nums.stages := by
  unfold testAll
  split
  · rename_i h
    rw [h]
    rfl
  · rename_i s rest h
    rw [h]
    show (stagesAll _ _ rest 0 s _ 1 _ _ _ D).rs.length + 1 = 1 + lenFrom s rest
    rw [length_stages, Nat.add_comm]

theorem count_toy (w : ℕ) (fr : Front Unit) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll Toy.J w fr C D).rs.length = (proximityTestKind guardedProximityTestParts Toy.J.p : Block T12 Unit).rounds.length :=
  (length_test _ _ _ _ _).trans (by decide +kernel)

theorem count_came (w : ℕ) (fr : Front Unit) (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll (ToyCame.came 0).J w fr C D).rs.length =
      (proximityTestKind guardedProximityTestParts (ToyCame.came 0).J.p : Block T12 Unit).rounds.length :=
  (length_test _ _ _ _ _).trans (by decide +kernel)

theorem termLen_KR : termLen piKRFull.nums.stages =
    (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds.length := by decide +kernel

/-- **At every job at `piKRFull`, `testAll` lists as many rounds as the block declares.** `piKRFull`
is the place of the key file's test on the ranges, written out as a closed term. -/
theorem count_KR (J : TestJob W X) (hJ : J.p = piKRFull) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) :
    (testAll J w fr C D).rs.length = (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds.length := by
  rw [length_test, hJ]
  exact termLen_KR

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.length_stages
#print axioms ProofFile.Honest.K12.length_test
#print axioms ProofFile.Honest.K12.count_toy
#print axioms ProofFile.Honest.K12.count_came
#print axioms ProofFile.Honest.K12.termLen_KR
#print axioms ProofFile.Honest.K12.count_KR
#print axioms ProofFile.Honest.K12.lenFrom
#print axioms ProofFile.Honest.K12.termLen
