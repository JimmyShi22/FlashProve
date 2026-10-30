-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/Share.lean: THE SMALLNESS TEST: THOSE OF ITS TESTS BEHIND THE
BATCHING THAT ASK "NOT 0" OR "ALL DIFFERENT" OF WEIGHTS, at the verifier's own state, with a name
for the one that says no. DEFINITIONS, WITH CODE. NO THEOREM. NOTHING IS CLAIMED ON COMPLETENESS,
SOUNDNESS OR HIDING.

Behind the batching the verifier gives no acceptance if a weight that should bind a committed entry
is 0, or if two row weights of a matrix are equal (docs/format/11-1-machinery.md, "Sampled values at
which a verifier gives no acceptance"). The honest prover of this folder sends all its messages at
such challenges too, and is refused. These functions say at which states that is so.
WHERE THE PROVER PROGRAM DOES OTHERWISE.
It sets a flag of its own where
a column's weight is 0
(prover/hiding/tail_gam.cuh:
`kh_gam`); by its comments no part of that proof is released.

WHERE EACH IS ASKED: at the state in front of the block that refuses, and at that block's own
challenges; nothing is run ahead. The block that draws the batching element also gathers and adds
the claims, and refuses where a column's weight is 0: `k8Front`. The block without a round behind it
runs the kind's tests on the ledger: `k8Share`.

  `k8Share nU s`   s: the verifier's state BEHIND the adding: it is the state in front of the block
      without a round that runs these tests. The first of seven tests that says no, by name. None
      if all say yes; outside a segment; and, for the last two, where the step in front of them
      refuses or a value that the verifier unwraps there lacks. Five are the conjuncts
      of "no weight that must not be 0 is 0" (`selfUnits`, `selfDigits`, `selfLinked`,
      `selfPlanes`, `selfSymbols`: Johnson/Desc/First/TailClaims/SelfTests.lean): THE VERIFIER's OWN
      FUNCTIONS, BY NAME. Two stand in the test by a second computation (`pieceWeightsHeld`,
      `tieWeightsHeld`: OnBytes/Model/Tail.lean): the verifier's own functions too, called behind
      the step that sets the rows' weights and at the arguments at which `rkSelfTestP` calls them
  `columnWeight tl chi mu c`   the weight of column c of matrix mu: the sum of its drawn entries
      under the powers of chi. A SECOND TEXT: it calls the verifier's `foldColumn` and `powers`,
      but where a column's entries begin is written out here as `foldSums` has it. THIS FILE HOLDS
      IT AGAINST `foldSums`' OWN SUMS BY NO THEOREM: tests by evaluation do, at a toy, in a file
      that the library may not hold (Johnson/Desc/ProofFile/Honest/K8/Toy.lean)
  `zeroColumnWeight tl chi`   the first column whose weight is 0
  `k8Front s ds`   s: the state IN FRONT OF the block that draws the batching element; ds: that
      block's challenges. The verifier asks the columns' weights while it gathers the claims, inside
      that block's decision: so this one is asked of the state in front and the drawn element. The
      drawn matrix lies in the state since the kind's own round

Limits. (1) `pieceWeightsHeld` and `tieWeightsHeld` also compare two computations of one weight:
they are taken whole, so a no of theirs need not come from a challenge's value.
(2) NOT ALL OF THE KIND's GUARDS ARE HERE. Left out are the guards on public numbers and sizes, and
SIX GUARDS ON VALUES that ask "two computations agree" or "nothing has turned", and no "not 0".
Five stand in the two tests behind the adding: `selfSlots` with the size in front of it;
`pointsHeld`; the two rows' weights on the array of digits against the powers of the batching
element; `planesWeightsHeld`; `readWeightsHeld` (SelfTests.lean: `selfTestP`, `rkSelfTestP`). One
stands at the gathering of the claims: no claim has put a weight on a slot of this test
(Johnson/Desc/First/TailClaims/Equations.lean: `eqAll`, "internal-f-tail-slot"). That an honest run
passes them is owed by whoever shows that the verifier accepts.
(3) `k8Share` asks each test whatever the tests in front of it in the verifier's text have said.
(4) Between the adding and the verifier's own call of these tests stand further runs. One of them,
this kind's own, writes one field of the state (`lsTail`); by reading, none of the seven tests, nor
the step in front of the last two, reads it. That no run between turns what
they read is not shown here.
(5) `zeroColumnWeight` asks every column of every matrix; the verifier asks, at that place, the
columns of the matrices on which a part of the vector of reads lies.
-/
import Johnson.Desc.K8.Honest.Fall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First (S tlForkP)
open VerifiableInference.Desc.First.TailClaims

/-- The five conjuncts of the verifier's first test on weights, in its order. -/
def k8First (tl : HTailF2) (nU : Array Nat) (F : Fork) : Option String :=
  if !selfUnits tl nU F then
    some "the smallness test: an entry of the vector of reads has the weight 0"
  else if !selfDigits tl F then
    some "the smallness test: a digit has the weight 0 in the lookup's rows"
  else if !selfLinked tl F then
    some "the smallness test: a digit has the weight 0 in the reads' or the ties' row"
  else if !selfPlanes tl F then
    some "the smallness test: a bit of a multiplicity has the weight 0"
  else if !selfSymbols tl F then
    some "the smallness test: a column of a matrix has the weight 0"
  else none

/-- The two tests of the second computation that ask "not 0" and "all different", behind the step
that sets the rows' weights. None where that step or a value that the verifier unwraps lacks. -/
def k8Second (tl : HTailF2) (F : Fork) : Option String :=
  match coefficientsP tl F, tl.heard, tl.joinObj9, tl.wants with
  | .ok G, some g, some jo, some (nbW, W) =>
    if !W.all (tl.pieceWeightsHeld G g (t2fKappaByText G.theta jo)) then
      some "the smallness test: a piece's weights"
    else if !(List.range tl.NM).all
        (tl.tieWeightsHeld G ((G.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L) then
      some "the smallness test: a tie's weights"
    else none
  | _, _, _, _ => none

/-- **Behind the adding.** nU: the plan's lengths of the vectors of reads at the place. -/
def k8Share (nU : Array Nat) (s : S) : Option String :=
  (tlForkP.get? s).bind fun q => (k8First q.1 nU q.2).or (k8Second q.1 q.2)

/-- The weight of column c of matrix mu at chi. -/
def columnWeight (tl : HTailF2) (chi : E) (mu c : Nat) : E :=
  foldColumn tl.cfF ((tl.cfFirst.getD mu 0 + c) * tl.tau) tl.tau (powers chi tl.tau)

/-- The first column whose weight at chi is 0: matrix, column. -/
def zeroColumnWeight (tl : HTailF2) (chi : E) : Option (Nat × Nat) :=
  (List.range tl.NM).findSome? fun mu =>
    (List.range (tl.mats.getD mu {}).k).findSome? fun c =>
      if isZeroE (columnWeight tl chi mu c) then some (mu, c) else none

/-- **In front of the block that draws the batching element**, at its one drawn element. -/
def k8Front (s : S) (ds : List Fmt.Drawn) : Option String :=
  match s.tl?, ds.map (·.elems) with
  | some tl, [[x]] =>
    (zeroColumnWeight tl (E.ofTriple x)).map fun _ =>
      "the smallness test: a column of the drawn matrix has the weight 0"
  | _, _ => none

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.k8First
#print axioms ProofFile.Honest.K8.k8Second
#print axioms ProofFile.Honest.K8.k8Share
#print axioms ProofFile.Honest.K8.columnWeight
#print axioms ProofFile.Honest.K8.zeroColumnWeight
#print axioms ProofFile.Honest.K8.k8Front
