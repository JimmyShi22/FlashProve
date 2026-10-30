-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/LastChain.lean: the last of a proof file's three chains, laid as one lot
of the description of a proof file. Two definitions. Nothing is proved here.

What it does. `secondSeat Z` reads the public plan `Z` and returns what the fold over blocks wants
for the last chain: the chain's state (`S₃`), its start, the chain itself, and the chain's share of
the file's last test (`fin₃`). The start and the chain come out of one call of `Third.last`, so they
cannot be made from different numbers. The start is made from the ends of the two earlier chains.
The chain has four parts, in this order: the second part of the linear claim (kind K14); the sources
of the trees that are taken over from the earlier chains; the request's own proximity test (kind
K12); the chain's end.
  p    the codes, the shape of the test on the table and the number of answers to a sample, as the
       planner has sized them.
  own  kind K12's block with the parts `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean), the same parts as
       at that kind's other three places, entered through the door `onOwn`, at the numbers that
       `H2U.placesOfMade` and `H2U.proximityTestParametersAt` read off the plan for the place W.
The result is `none` where these numbers cannot be made from the plan.
`secondSeatOf Z N` is the lot itself, at given numbers `N` of that kind's four places. It has a name
of its own so that a theorem which is typed at the chain's state can be carried to the lot's value:
`(secondSeatOf Z N).σ` is `S₃` by unfolding, which cannot be said of a record inside a `match`.

The two fields that are written out.
  fileOk := true    What this lot asks of the plan is asked by its blocks' own `planOk`: for
                    K14's second part the codes' lengths, `linOk`, and that the shape does not split
                    the row; for the end that the last round in front counts no claims; for K12's
                    block that kind's own test. The file's test on the plan asks `planOk` of every
                    block of the chain. Six further conditions on this chain are asked elsewhere: in
                    the `fileOk` of the shared chain's lot, through `OkD.AtC.beside`
                    (Johnson/Desc/OnPlan/OkBesideC.lean): `stagesW`, `firstW`, `n4`, `n6`, `n8` and
                    `remadeW`. The first five read the plan's parameters as they are read back, not
                    the sized numbers that this chain's blocks act on. `remadeW` runs the planner's
                    routine for this chain again at the sized numbers and compares its entries with
                    those read back.
  standIns := []    K14's second part, the taken trees' sources and the end have their decisions
                    written out and call no step of `verify-on-bytes`'s runner. For K12's block that
                    is said by that kind's own files, not here.

Where the text comes from. The definition is taken over word for word from a text of this project
for the same fold, but for the definition's name, the imports, the
string `lot`, and the parts' name: that text had `proximityTestParts` (Johnson/Desc/K12/Join.lean), which asks
fewer tests than `guardedProximityTestParts`.

Limits. (1) No law is stated or proved here: that the chain's blocks are sound is not claimed. (2)
Functions of `verify-on-bytes` are still called by name: the start and K14's second part call
`Codes.lengthsOk`, `linOk` and `linDotRow`. (3) That no text which was weakened for a test lies
among the imports has been looked at by the imported modules' names alone.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.LotCore
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.Third.Border
import Johnson.Desc.Third.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Third
open ProofFile

/-- The lot at given numbers of kind K12's four places. -/
def secondSeatOf (Z : Pub) (N : H2U.Places4) : SecondSeat :=
  let z := Z.p.chains.made.sized.proof
  let p := VerifiableInference.Desc.Third.p₁₄Z z.set z.codes z.batch
  let own := VerifiableInference.Desc.K12.Seat.onOwn
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W))
  let made := VerifiableInference.Desc.Third.last p VerifiableInference.Desc.Third.firstOfS
    VerifiableInference.Desc.Third.sharedOfEnd own
  { lot :=
      "the last chain: K14's second part, the taken trees' sources, K12's own block, the end"
    σ := VerifiableInference.Desc.Third.S₃
    start := made.start
    chain := made.chain
    done := VerifiableInference.Desc.Third.fin₃
    fileOk := true
    standIns := [] }

/-- The proof file's last chain as one lot. `none` where the plan does not give the numbers of the
place W. -/
def secondSeat (Z : Pub) : Option SecondSeat :=
  match H2U.placesOfMade Z.made with
  | .ok N => some (secondSeatOf Z N)
  | .error _ => none

end P2Third
