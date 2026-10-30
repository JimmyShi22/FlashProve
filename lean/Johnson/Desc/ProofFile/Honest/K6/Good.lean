-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Good.lean: two tests with code on the challenges of the
sub-protocol "the output head's own rounds" (Johnson/Desc/Kinds/Head.lean), general in the place's
public numbers. Definitions with code; no theorem.

Why. By a reading of its text the sub-protocol's own decision compares no sent value with anything.
But behind the segment's batching the verifier asks tests on values that are made of this
sub-protocol's challenges, and at some challenges such a value is 0 whatever the batching element
is. Whoever counts at how many lists of challenges an honest run is refused needs these challenges
named. Two of the verifier's tests are meant:
  (1) "every sent scalar stands in a claim" (Johnson/Desc/First/Batch/Sums.lean: `freeSlot`): each
      scalar's coefficient in the sum of all claims is not 0;
  (2) "no weight on the reads' row is 0" (Johnson/Desc/First/TailClaims/SelfTests.lean:
      `selfLinked`): each weight is a sum, over the tables of reads on a matrix, of a power of the
      batching element times the table's weight, which for most tables is an equality weight of a
      point that is made of challenges.

  `headLs`            the logarithm of the number of features in a block
  `goodK6Clauses`, `goodK6`, `goodK6Says`, `goodK6Events`       for (1)
  `goodK6NzClauses`, `goodK6Nz`   for (1): four clauses more, which are not counted
  `linkedK6Clauses`, `linkedK6`, `linkedK6Says`, `linkedK6Events`   for (2)
  `bothK6Events`      how many events the two have together

The first count as a share in the form of Honest/Frame.lean stands in Honest/K6/GoodOdds.lean, so
that this file hangs on no frame.

Each test is a list of named clauses, one for each drawn element that it reads; the test says yes if
all hold; `...Says` gives the name of the first that fails.

For (1). A masked sumcheck's own scalars stand in the one claim that it leaves, a variable's two
under the variable's challenge and its square: so a variable's challenge 0 leaves both without a
claim of this sub-protocol's. Its last three scalars stand there under 1, the element of the round
in the further variable, and that element's square. The claimed sums of the third and the fourth
sumcheck stand in that claim under the element drawn at the sumcheck's beginning, and once more in
the claim on the lookup's key vectors, under a weight that is the lookup's. Every other scalar of
the sub-protocol but one has a coefficient 1, -1 or -2 in some claim. The one: the fourth sumcheck's
second end value, which no claim of this sub-protocol names. `goodK6`: no variable's challenge of
the four sumchecks is 0, nor the element at the beginning of the third and of the fourth. `goodK6`
HAS NO CLAUSE ON THE FOUR ELEMENTS OF THE ROUNDS IN THE FURTHER VARIABLE: they are drawn by the rule
that never gives 0 (asked of a round by `drawsMarkedNonzeroHaveNonzeroWords`, Johnson/Desc/Block.lean, and of a list of
challenges by `drawFit`, Honest/Frame.lean), so "is 0" is no event there and is not counted.
`goodK6Nz` asks it of them: so whoever wants "every scalar but one stands in a claim" of a bare list
of challenges asks both tests, and needs no premise from outside but that on the words (Limits).

For (2). An equality weight is a product with a factor x or 1 - x for each coordinate x of its
point: it is 0 just if a coordinate is 0 at a bit 1, or 1 at a bit 0. Of the matrices that the
head's tables read, three have a table whose point is made of this sub-protocol's challenges alone:
the stream's (the last ls + lt challenges of the first sumcheck), the activations' (the first lt of
the fourth), the row's (the point on the positions). `linkedK6`: none of these coordinates is 0 or
1. Then that table's weights are all other than 0.

Limits. NO LAW TIES EITHER TEST TO THE VERIFIER's TESTS: which scalar stands in which claim, and
which table has which point, are readings of the verifier's text; Honest/K6/ToySlots.lean and
Honest/K6/GoodToy.lean hold them at one small size. EACH SAYS NO AT MORE LISTS THAN THOSE AT WHICH
ITS OWN VALUE IS 0 AT EVERY BATCHING ELEMENT: `goodK6` says no where the element at the beginning of
the third or fourth sumcheck is 0, though the scalar then still stands in a claim unless a weight of
the lookup's is 0 too; `linkedK6` says no at one coordinate, though a weight is 0 at every batching
element only where ALL tables on a matrix vanish at one row of cells, which takes two challenges at
once for the stream and the activations, four for the row. NEITHER SAYS ANYTHING OF THE BATCHING
ELEMENT: where they say yes (the first together with `goodK6Nz`) a coefficient or weight is a
polynomial in it that is not the zero polynomial, and can still come to 0. Neither covers the scalar
that no claim of this sub-protocol names, the matrices whose tables are made of the lookup's
challenges alone, or any other test of the verifier's. "Is 0" and "is 1" compare words: they mean
the field's 0 and 1 only where every word of a challenge is below the prime. That is asked of a
view's drawn elements by `viewWordsBelowPrime` (Johnson/Desc/Block.lean) and of a list of challenges by
`drawFit` (Honest/Frame.lean); whether the rule by which challenges are drawn always yields such
words was not looked at. A round that the list does not hold, or that draws nothing, counts as 0, so
a list that is too short fails. Where a block had more features than there are with padding (ls
above lPd) the second test would have fewer clauses, in silence. The counts say how many elements a
test reads, not which: which, is held at one small size (Honest/K6/GoodToy.lean). They are counts of
events "one named element has one named value"; what share of all lists that is, is not said here.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.HeardWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E isZeroE zeroE oneE)
open VerifiableInference.Desc.Kinds (Point Head.Par)

/-- The logarithm of the number of features in a block. -/
def headLs (p : Head.Par) : Nat := p.sizes.ls

/-- One clause for each coordinate of a point: its name, and whether ok holds of it. what: the
point's name; says: what the clause asks. -/
def headClausesOn (what says : String) (ok : E → Bool) (z : Point) : List (String × Bool) :=
  z.toList.zipIdx.map fun x => (what ++ ", number " ++ toString x.2 ++ ", " ++ says, ok x.1)

/-- The name of the first clause that fails. -/
def headFirstNo (l : List (String × Bool)) : Option String := (l.find? fun c => !c.2).map (·.1)

/-! ## 1 For "every sent scalar stands in a claim" -/

/-- **The clauses**, in the order of the rounds but for the last two: no variable's challenge of the
four masked sumchecks is 0; nor is the element drawn at the beginning of the third and of the
fourth. own: the sub-protocol's own challenges, from its first round on. -/
def goodK6Clauses (p : Head.Par) (own : List Fmt.Drawn) : List (String × Bool) :=
  let lt := headLt p
  let m := headLPd p + lt
  let vars (what : String) (i n : Nat) : List (String × Bool) :=
    headClausesOn (what ++ ": a variable's challenge") "is not 0" (!isZeroE ·) (headSumR p i n own)
  let first (what : String) (i : Nat) : String × Bool :=
    (what ++ ": the element drawn at its beginning is not 0",
      !isZeroE (elemOf own (headInFront p i)))
  vars "the sumcheck on the squares" 2 m ++ vars "the sumcheck on the products" 5 lt ++
    vars "the sumcheck on the stream times the reciprocal" 6 lt ++
    vars "the head's own sumcheck" 7 m ++
    [first "the sumcheck on the stream times the reciprocal" 6, first "the head's own sumcheck" 7]

/-- **The test.** -/
def goodK6 (p : Head.Par) (own : List Fmt.Drawn) : Bool := (goodK6Clauses p own).all (·.2)

/-- The first clause that fails; nothing where the test says yes. -/
def goodK6Says (p : Head.Par) (own : List Fmt.Drawn) : Option String :=
  headFirstNo (goodK6Clauses p own)

/-- How many events "one named drawn element is 0" the test's no is made of. -/
def goodK6Events (p : Head.Par) : Nat := 4 * headLt p + 2 * headLPd p + 2

/-- **Four clauses more, not counted among the events**: the element of each sumcheck's round in the
further variable is not 0. That round stands behind the variables' rounds. The rule by which it
draws never gives 0. -/
def goodK6NzClauses (p : Head.Par) (own : List Fmt.Drawn) : List (String × Bool) :=
  let lt := headLt p
  let m := headLPd p + lt
  let last (what : String) (i n : Nat) : String × Bool :=
    (what ++ ": the element of the round in the further variable is not 0",
      !isZeroE (elemOf own (headInFront p i + 1 + n)))
  [last "the sumcheck on the squares" 2 m, last "the sumcheck on the products" 5 lt,
    last "the sumcheck on the stream times the reciprocal" 6 lt, last "the head's own sumcheck" 7 m]

/-- **The test on these four.** -/
def goodK6Nz (p : Head.Par) (own : List Fmt.Drawn) : Bool := (goodK6NzClauses p own).all (·.2)

/-! ## 2 For "no weight on the reads' row is 0" -/

/-- Neither 0 nor 1. -/
def headNotBit (x : E) : Bool := !isZeroE x && x != oneE

/-- **The clauses**: none of these coordinates is 0 or 1: the last ls + lt challenges of the first
sumcheck's variables; the first lt of the fourth's; the point on the positions. -/
def linkedK6Clauses (p : Head.Par) (own : List Fmt.Drawn) : List (String × Bool) :=
  let lt := headLt p
  let lPd := headLPd p
  let of_ (what : String) (z : Point) : List (String × Bool) :=
    headClausesOn what "is neither 0 nor 1" headNotBit z
  of_ "the stream's table: of the last challenges of the sumcheck on the squares"
      ((headSumR p 2 (lPd + lt) own).extract (lPd - headLs p) (lPd + lt)) ++
    of_ "the activations' table: of the first challenges of the head's own sumcheck"
      (headSumR p 7 lt own) ++
    of_ "the row's table: of the point on the positions"
      ((Array.range lt).map fun j => (headPV own).getD j zeroE)

/-- **The test.** -/
def linkedK6 (p : Head.Par) (own : List Fmt.Drawn) : Bool := (linkedK6Clauses p own).all (·.2)

/-- The first clause that fails; nothing where the test says yes. -/
def linkedK6Says (p : Head.Par) (own : List Fmt.Drawn) : Option String :=
  headFirstNo (linkedK6Clauses p own)

/-- How many events "one named drawn element is 0" or "is 1" the test's no is made of. -/
def linkedK6Events (p : Head.Par) : Nat := 2 * (headLs p + 3 * headLt p)

/-- The events of the two tests together, each counted once. The first test's: "is 0" at the 4 lt +
2 lPd variables' challenges and at two elements more. The second test's: "is 0" and "is 1" at ls + 3
lt elements. Both tests have "is 0" at the ls + lt last challenges of the first sumcheck and at the
lt first of the fourth: these ls + 2 lt events are counted with the first test. New with the second:
"is 1" at these ls + 2 lt elements, and "is 0" and "is 1" at the lt coordinates of the point on the
positions: ls + 4 lt. -/
def bothK6Events (p : Head.Par) : Nat := goodK6Events p + headLs p + 4 * headLt p

end ProofFile.Honest.K6
