-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/LinkedTest.lean: a test with code on the challenges of the
sub-protocol "the output head's own rounds" (K6), `linkedK6T`, with the numbers of the rounds that
it reads and a stated number. Five definitions with code; no theorem.

Why a file of its own. Honest/K6/LinkedMark.lean lays this test, turned round, as a mark, and proves
what is owed for it, over many files. Whoever only names the test, its rounds or its number imports
this file, which imports Honest/K6/Good.lean and Honest/K6/GoodOdds.lean alone.

The test. Behind the segment's batching the verifier asks that no weight on the reads' row and on
the ties' row is 0 (`selfLinked`, Johnson/Desc/First/TailClaims/SelfTests.lean). Honest/K6/Good.lean
says how such a weight on the reads' row hangs on this sub-protocol's challenges, and has a test on
the challenges for it, `linkedK6`: no coordinate of three points, one for each of three committed
matrices, is 0 or 1. `linkedK6T` has that test's first two groups of clauses, for the stream's
matrix and the activations'. In the third group, for the row's matrix, it reads the challenges of
the sumcheck on the products, one element a round, in place of the point on the positions, all of
whose coordinates one round samples. The row's matrix has a table of reads for either: of the twelve
tables (`readsNeed`, Johnson/Stored/HeadSeatAt.lean) the seat's reader in that file lays "hr@P_V"
for `rowAtPV` and "hr@r_tV" for `rowAtProducts`. So each coordinate that `linkedK6T` reads is the
first element of a round of its own.

  `linkedK6TClauses`, `linkedK6T`, `linkedK6TSays`   the test
  `linkedRounds`      the numbers of the rounds that it reads
  `linkedK6TOdds`     the stated number

Limits. NO THEOREM TIES THE TEST `linkedK6T` TO `selfLinked`, NOR TO `linkedK6`: which table of
reads has which point, and that the table's weights are other than 0 where no coordinate of its
point is 0 or 1, are readings of the verifier's text. EVEN BY THESE READINGS, THAT THE TEST
`linkedK6T` ACCEPTS DOES NOT GIVE `selfLinked`. It says nothing of the batching element: where it
accepts, a weight on the reads' row is a polynomial in that element that is not the zero polynomial,
and can still come to 0. It says nothing of the ties' row. It does not cover the matrices whose
tables are made of the lookup's challenges alone. And it rejects at more lists of challenges than
those at which a weight is 0 at every batching element. That `linkedRounds` names just the rounds
that the test reads is proved in Honest/K6/LinkedMark.lean (`linkedK6T_iff`), which is not in the
library, not here. `linkedK6TOdds` is a number that is written down, no bound: nothing holds it
against the test in a space of challenges. All limits of Honest/K6/Good.lean hold here too.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Good
import Johnson.Desc.ProofFile.Honest.K6.GoodOdds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc.Kinds (Point Head.Par)

/-- **The clauses**: none of these coordinates is 0 or 1: the last ls + lt challenges of the first
sumcheck's variables; the first lt of the fourth's; the lt of the second's: in the order of the
three matrices, not of the rounds. -/
def linkedK6TClauses (p : Head.Par) (own : List Fmt.Drawn) : List (String × Bool) :=
  let lt := headLt p
  let lPd := headLPd p
  let of_ (what : String) (z : Point) : List (String × Bool) :=
    headClausesOn what "is neither 0 nor 1" headNotBit z
  of_ "the stream's table: of the last challenges of the sumcheck on the squares"
      ((headSumR p 2 (lPd + lt) own).extract (lPd - headLs p) (lPd + lt)) ++
    of_ "the activations' table: of the first challenges of the head's own sumcheck"
      (headSumR p 7 lt own) ++
    of_ "the row's table: of the challenges of the sumcheck on the products"
      (headSumR p 5 lt own)

/-- **The test.** -/
def linkedK6T (p : Head.Par) (own : List Fmt.Drawn) : Bool := (linkedK6TClauses p own).all (·.2)

/-- The first clause that fails; nothing where the test `linkedK6T` accepts. -/
def linkedK6TSays (p : Head.Par) (own : List Fmt.Drawn) : Option String :=
  headFirstNo (linkedK6TClauses p own)

/-- **The numbers of the rounds whose first sampled element the test reads**, rising: of the first
sumcheck's variables' rounds those from number lPd - ls on (all, where ls is above lPd); the
second's lt; the first lt of the fourth's. -/
def linkedRounds (p : Head.Par) : List Nat :=
  (List.range (headLPd p + headLt p - (headLPd p - headLs p))).map
      (headInFront p 2 + 1 + (headLPd p - headLs p) + ·) ++
    (List.range (headLt p)).map (headInFront p 5 + 1 + ·) ++
    (List.range (headLt p)).map (headInFront p 7 + 1 + ·)

/-- **The stated number**: two events, "is 0" and "is 1", at each round that the test reads, of the
number of elements of the extension field. A stated number, no bound. -/
def linkedK6TOdds (p : Head.Par) : Odds := ⟨2 * (linkedRounds p).length, Code.pGold ^ 3⟩

end ProofFile.Honest.K6
