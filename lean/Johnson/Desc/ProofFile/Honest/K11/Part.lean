-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Part.lean: the honest side of the kind "the merge of the claims on
the weights" (K11), in the form of Honest/Frame.lean and Honest/Side.lean. The kind's own text does
not write what an honest prover sends (Johnson/Desc/First/Fork/MergeKind.lean, under SENDS); this
file writes it, in that form, BUT FOR ONE PARAMETER THAT IS OPEN HERE: how the claims are made
(`claims`; see Limits). Definitions with code; no theorem.

What is sent (docs/format/11-1-machinery.md, a page of the format's, which this library may not
hold: "The merge" and "The merge: values and claim"). lk + 4 rounds at a matrix with 2 ^ lk columns.
In the first, "BAT-sigma", nothing. Then a masked sumcheck over the lk column bits, the highest
first, each summed plainly, with three coefficients a round; one further variable of degree 1; one
end value: 2 lk + 3 scalars. The sumcheck's moves are `sumPart`'s (Honest/Sum.lean); what is summed
is Johnson/Desc/K11/Honest/Summand.lean's.

The row is cut in two parts, of 1 and of lk + 3 rounds.
The coins. No part takes a coin of its own. The second spends two runs of other parts' coins: 2 lk +
2 entries of the segment's mask row: the hiding polynomial's coefficients; and ONE entry of the
index-mask message, which is laid over the end value. By the format's page the first are the entries
under the numbers of the sumcheck's own scalars in front of the end value, and the second is that
message's next free entry; HERE EACH RUN HAS A NAME AND A COUNT ALONE: which entries they are is the
book's to say. The part carries no run. THE CLAIMED SUM's OWN MASK ENTRIES ARE NOT READ: by the
format's page the honest round polynomial has a term with them, and that term lies wholly in the
coefficient that is not sent (the head of Honest/Sum.lean).
The stops. None.
What is read of the input: of the index the entries of the committed matrix, in the rows of the
units that the claims name, at all columns; of the public instance what `claims` reads; of the
witness nothing.

  `HeadMergeAsk`                     what the sumcheck's part needs of the input
  `headMergeShape`, `headMergeTerms`, `headMergeJob`   the call's shape; the terms of the sum in a
                                     session; the summand, for `sumPart`
  `headMergeDraw`, `headMergeSum`    the part of the round that sends nothing; the sumcheck's part
  `headMergePlace`, `headMergeRow`, `headMergeHalf`, `headMergeLot`   the row at its place; under
                                     the lot's name
  `headMergeDrawSim`, `headMergeSims`, `headMergeSided`, `headMergeSide`   a simulator beside each
                                     part; the side

Limits. `claims` IS A PARAMETER, OPEN HERE: the function that makes the claims on the weights of the
public instance and the challenges heard in front of the place. The verifier's text reads the claim
off its state, where a quiet step in front has laid it; nothing here holds `claims` against that.
Honest/K11/Claims.lean fills it with the function that this quiet step itself calls, up to four
fields of what the head's rounds heard; `headFourN` (Honest/K11/ClaimsN.lean) fills them. The kind's
block is the head's, with one claim; the row takes any number, claim
number i under the power i of the batching element. A PREMISE ON THE LAYOUT, WHICH NOTHING HERE
ASKS: that what is summed is the merge's summand is meant at a layout whose units have the library's
`UnitOK` (Johnson/Road/FormsKeysWOk.lean); at another layout it need not be so (the head of
Johnson/Desc/K11/Honest/Summand.lean). Nothing is said of `Good` at this side. The simulators are
data.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Lot.K11
import Johnson.Desc.K11.Honest.Summand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E zeroE)
open OnBytes.Model (WsLay WsClaim)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Honest (Term termsOf roundAt endAt)

/-- What the sumcheck's part needs of the prover's input. -/
structure HeadMergeAsk where
  /-- the claims on the weights: of the challenges heard in front of the place -/
  claims : List Fmt.Drawn → List WsClaim
  /-- the committed matrix, by row and column -/
  entry : Nat → Nat → E

/-- The call's shape: no lead; lk variables, each summed plainly, three coefficients a round; degree
1 in the further variable; one end value. -/
def headMergeShape (lk : Nat) : Call := ⟨0, List.replicate lk (.plain 3), some ⟨1, 1⟩⟩

/-- The terms of the sum in a session. The last challenge in front of the sumcheck is the element
that batches the claims; those in front of it stand in front of the place. -/
def headMergeTerms (lay : WsLay) (w : HeadMergeAsk) (fr : Front Unit) : List Term :=
  termsOf lay w.entry ((drawnE fr.heard).getLastD zeroE) (w.claims fr.heard.dropLast)

/-- **The summand**, for `sumPart`. The whole summand is the one map whose value at the challenges
is shown: in the further variable it is that value plus Y times the end value's mask entry.
On the letter m of `inY`: «m: the end values' mask
entries as sumPart hands them: by the shape's one end value a list of one (endCoins at some ⟨1, 1⟩
is coinsE of a Cs ⟨0, 1⟩). `headD zeroE` is for totality alone: at an empty list the coefficient of
Y would be 0, an end value without a mask; no lemma of this file says that the list is never
empty.» -/
def headMergeJob (lay : WsLay) : SumJob HeadMergeAsk Unit :=
  { shape := headMergeShape lay.lk
    points := fun _ _ => []
    lead := fun _ _ => []
    round := fun w fr rs => roundAt (headMergeTerms lay w fr) rs
    inY := fun w fr rs m => [endAt (headMergeTerms lay w fr) rs, m.headD zeroE]
    ends := fun w fr rs => [endAt (headMergeTerms lay w fr) rs] }

/-- The part of the round "BAT-sigma": nothing is sent: the frame's `quietPart`
(Honest/ForKinds.lean). -/
def headMergeDraw {V W X : Type} : Part V W X := quietPart

/-- The kind's place, of the numbers that its block takes. -/
def headMergePlace (P : HeadMergeP) : Place := ⟨1, some P.link, P.piece, .K11⟩

variable {W₀ Rc Xi Tr X : Type}

/-- **The sumcheck's part**, seated: the row's part number 1. claims: see the head. weights: how the
index is read. -/
def headMergeSum (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  (sumPart (runName maskRowRun ⟨headMergePlace P, 1⟩ "sum")
    (runName indexMaskRun ⟨headMergePlace P, 1⟩ "ends") (headMergeJob P.lay) :
      Part Unit HeadMergeAsk Unit).lift
    (fun _ => ()) (fun i => ⟨claims i.x, fun r c => eOfF ((weights i.w₀).entry r c)⟩)
    (fun _ => ()) fun x _ => x

/-- **The row.** -/
def headMergeRow (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  [headMergeDraw, headMergeSum P claims weights]

/-- **The kind's half.** -/
def headMergeHalf (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) :
    KindHalf HeadMergeP (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun P => ⟨headMergePlace P, headMergeRow P claims weights⟩

/-- **The lot's honest side**: the half at the numbers at which the lot lays the kind's block
(`K11.parOf`, Johnson/Desc/ProofFile/Lot/K11.lean). THE NAME IS WRITTEN A SECOND TIME HERE: the
lot's own takes the public part as an argument. -/
def headMergeLot (claims : Pub → Ground → Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  { name := "the merge of the weights' claims"
    halves := fun Z G => [headMergeHalf (claims Z G) weights (_root_.K11.parOf Z G)] }

/-- Beside the part of the round that sends nothing: it yields one round without an item: the
frame's `quietSim`. -/
def headMergeDrawSim (P : HeadMergeP) : Sim Xi := quietSim ⟨headMergePlace P, 0⟩

/-- A simulator beside each part; beside the sumcheck: `sumSim`. -/
def headMergeSims (P : HeadMergeP) : List (Sim Xi) :=
  [headMergeDrawSim P, sumSim ⟨headMergePlace P, 1⟩ (headMergeShape P.lay.lk)]

/-- The row, each part with its simulator. -/
def headMergeSided (P : HeadMergeP) (claims : Xi → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi) :=
  (headMergeRow P claims weights).zip (headMergeSims P)

/-- **The side**: that row beside the member of a description's first chain that stands at the
place; `none` if none does. bs: that chain's list. -/
def headMergeSide {S Cl : Type} (bs : List (Block S Cl)) (P : HeadMergeP)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) :
    Option (Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) :=
  Side.seated bs (headMergePlace P) (headMergeSided P claims weights)

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.HeadMergeAsk
#print axioms ProofFile.Honest.K11.headMergeShape
#print axioms ProofFile.Honest.K11.headMergeTerms
#print axioms ProofFile.Honest.K11.headMergeJob
#print axioms ProofFile.Honest.K11.headMergeDraw
#print axioms ProofFile.Honest.K11.headMergePlace
#print axioms ProofFile.Honest.K11.headMergeSum
#print axioms ProofFile.Honest.K11.headMergeRow
#print axioms ProofFile.Honest.K11.headMergeHalf
#print axioms ProofFile.Honest.K11.headMergeLot
#print axioms ProofFile.Honest.K11.headMergeDrawSim
#print axioms ProofFile.Honest.K11.headMergeSims
#print axioms ProofFile.Honest.K11.headMergeSided
#print axioms ProofFile.Honest.K11.headMergeSide
