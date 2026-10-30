-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Fall.lean: THE SMALLNESS TEST: ONE OF ITS TESTS BEHIND THE BATCHING, "no
entry of the vector of reads has the weight 0", AS A PLAIN FUNCTION. DEFINITIONS, WITH CODE. NO
THEOREM. NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

The test. Behind the batching the verifier asks that every entry of the vector of reads has a weight
other than 0 in the segment's one equation, all the segment's claims counted (`selfUnits`,
Johnson/Desc/First/TailClaims/SelfTests.lean).
WHY IT HAS A FILE OF ITS OWN. BY READING, NOT BY A THEOREM: in a feed-forward segment some of these
weights have a scalar as a factor that the prover has sent under a mask (OnBytes/Model/Tail.lean, at
`selfTestF`: "What a weight is made of"), and an honest prover draws the mask. So there the test's
answer can hang on the prover's own coins. Of this kind's tests it is the only one of which that was
found; other kinds' tests are not spoken of here.

  `unitWeightAt F t x`   the weight of entry x of the array number t. It is `selfUnits`' own
      reading, written out once more, so that statements can name one weight:
      Johnson/Desc/K8/Honest/FallLaw.lean ties the two (`selfUnits_iff`, `zeroUnit_iff`)
  `zeroUnit tl nU F`     `selfUnits` says no
  `zeroUnitAt nU s`      the same at the verifier's state in the first chain, behind the adding
  `fallBehind batch nU s ds`   `zeroUnitAt`, asked from the state s in front of the block that
      draws the batching element and that block's own challenges ds (`askBehind`,
      Johnson/Desc/K8/Honest/Behind.lean)
  `fallTest b nU`        the same at a block, with words for a refusal
They are handed no coin, no witness and no oracle message: the state holds what was sent in the
clear and what was drawn.
WHAT IT DOES NOT HOLD. It is one of the kind's tests on values behind the adding. Beside it the
verifier asks four more of the form "no weight is 0", and tests by a second computation
(Johnson/Desc/First/TailClaims/SelfTests.lean: `selfTestP`, `rkSelfTestP`). The functions here are
for statements on this one test alone.

Limits. (1) The conjunct is asked by itself: the verifier's refusal bears one name for five
conjuncts, so the name could not tell this one from the other four. (2) Where the block's own
decision refuses, `fallBehind` says false: such challenges are another set's matter. (3) Between
the adding and the verifier's own call of the test stand further runs; that none of them turns what
`selfUnits` reads is not said here. (4) Outside a segment `zeroUnitAt` says false.

-/
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.K8.Honest.Behind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims

/-- The weight that the one equation puts on entry x of the array number t of a segment's list: a
vector lies in its array row by row, K entries to a row. -/
def unitWeightAt (F : Fork) (t x : Nat) : E :=
  (weightsOf F t (x / (F.trees.getD t {}).K)).getD (x % (F.trees.getD t {}).K) zeroE

/-- Some entry of a vector of reads has the weight 0: the verifier's test `selfUnits` says no. -/
def zeroUnit (tl : HTailF2) (nU : Array Nat) (F : Fork) : Bool := !selfUnits tl nU F

/-- The same at the verifier's state. nU: the plan's lengths of the vectors of reads at the place.
-/
def zeroUnitAt (nU : Array Nat) (s : S) : Bool :=
  match tlForkP.get? s with
  | some q => zeroUnit q.1 nU q.2
  | none => false

/-- The same, asked from the state in front of the block that draws the batching element. batch:
that block's decision, at rounds as a view shows them. -/
def fallBehind (batch : S → List Fmt.RoundView → Except String S) (nU : Array Nat) (s : S)
    (ds : List Fmt.Drawn) : Bool :=
  askBehind batch (zeroUnitAt nU) s ds

/-- The same at a block, which is owed no column; with words. -/
def fallTest {Cl : Type} (b : Block S Cl) (nU : Array Nat) (s : S) (ds : List Fmt.Drawn) :
    Option String :=
  if fallBehind (fun t rs => b.decide t rs []) nU s ds then
    some "the smallness test: an entry of the vector of reads has the weight 0"
  else none

end VerifiableInference.Desc.First.K8.Honest
