-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Rounds.lean: how the checks of the model's sub-proofs read the request's chain.

All sub-proofs of a request share one chain, the one that the protocol's blocks use
(OnBytes/Iop/Ground.lean). So whatever the check of a sub-proof receives or draws goes through the
type Blk of that file. The checks add a state of their own to Blk (SubM, OnBytes/Model/Hide.lean).
Nothing here reads bytes or calls the hash.

Terms. OnBytes/Iop/Ground.lean explains chain, plan, view, dry run, oracle message and strict reader
(the reader itself is OnBytes/Chain/Reader.lean). The channel is the part of Blk's state that walks
the plan and the view (Chan, in Ground.lean).

By convention the check of a sub-proof receives scalars and draws only through the ten functions of
this file; Lean does not enforce this. A link's oracle messages go through ChainCheck
(OnBytes/Model/ReqChain.lean). The ten have the names of the routines of
verifier/src/vf_transcript_calls.h. There each only calls a routine of vf_transcript_channel.h.
The last part holds what the rounds of all sumchecks share (verifier/src/vf_sumcheck_receive.h).

Main definitions: RoundName, trRead, trSum, trAnswer, trAnswerNotZero, trPoint, trBatch,
trBatchOpen, trBatchRows, trEmpty, trTrits, RoundForm, roundValues, sumcheckSlots,
sumcheckSlotsDegrees, layerSlots, roundDraw.

What this file does not claim. No theorem is stated here. Two tests of the C++ channel have no
counterpart: that trSum is the last call before the draw of the name pscEpsilon (see trSum), and the
comparison of the number of combinations of the matrix of trTrits by itself (see trTrits).
-/
import OnBytes.Iop.Ground
import OnBytes.Params.Names
import OnBytes.Model.Frame

namespace OnBytes.Model

/-! ## The names of the rounds -/

/-- The rounds that the check of a sub-proof can close, named after the protocol's blocks: psc is
the masked sumcheck (OnBytes/Model/Psc.lean), lkp the lookup, bat the combination of many rows into
one. -/
inductive RoundName where
  /-- the element that joins a hiding polynomial to a claim -/
  | pscEpsilon
  /-- the challenge of a round of a sumcheck -/
  | pscRound
  /-- the challenge of the extra round of a sumcheck, over the end values -/
  | pscY
  /-- the point on the line through two points -/
  | line
  /-- the point of a test that a vector is zero -/
  | zero
  /-- the element that batches rows -/
  | batSigma
  /-- a lookup's challenge -/
  | lkp
  /-- a lookup's shift -/
  | lkpShift
  /-- the point that joins the planes of a lookup's multiplicities; plane j holds bit j of each -/
  | lkpPlanes
  /-- the point at which a forest of product trees is entered. No check closes a round under this
  name; it is kept because the C++ list has it -/
  | forestPoint
  /-- the elements, one or more, that join several claims -/
  | join
  /-- the round of a sumcheck's end values, to which the verifier says nothing -/
  | pscValues
  deriving DecidableEq, Repr, Inhabited

/-- The round's name in the plan. lkpPlanes, forestPoint and join share the plan's name JOIN. -/
def RoundName.name : RoundName → String
  | .pscEpsilon => "PSC epsilon"
  | .pscRound => "PSC round"
  | .pscY => "PSC Y"
  | .line => "LINE"
  | .zero => "ZERO"
  | .batSigma => "BAT-sigma"
  | .lkp => "LKP"
  | .lkpShift => "LKP shift"
  | .lkpPlanes => "JOIN"
  | .forestPoint => "JOIN"
  | .join => "JOIN"
  | .pscValues => "PSC values"

/-- The name in the plan of the round that draws the matrix of the smallness test. RNG is the
protocol's block for a range check. -/
def rngName : String := "RNG"

/-! ## Closing a round against the plan -/

/-- Closes the open message's round. The name must be that of the plan's next entry, and kind the
kind that the format gives this name. The entry must draw elems elements, notZero of them by the
rule that never gives 0, entries matrix entries, and no positions. -/
def closeAs (name : String) (kind : Fmt.Kind) (elems notZero entries : Nat) : Blk Fmt.Drawn := do
  Blk.must (Params.kindOf name == some kind)
  let d ← Blk.close name kind notZero
  let e ← Blk.lastEntry
  Blk.must (e.drawE == elems && e.trits == entries && e.poss == 0)
  pure d

/-- The one element that a round has drawn. -/
def oneOf (d : Fmt.Drawn) : Blk E :=
  match d.elems with
  | [x] => pure (E.ofTriple x)
  | _ => Blk.fail

/-- Fails as internal-batching-bare if r is batSigma. The round whose element combines rows is to be
closed only by trBatch or trBatchOpen, so that the number of rows is compared wherever the plan's
entry counts rows. -/
def noBatching (r : RoundName) : Blk Unit := mustAs "internal-batching-bare" (r != .batSigma)

/-- The one name that this file itself gives to a refusal. It is the C++ verifier's. The other
failures of this file have no name of their own: the conditions of closeAs, oneOf and trTrits fail
under the word "refused", and the channel's under "plan" or "view-shape" (OnBytes/Iop/Ground.lean).
OnBytes/Model/StagesNames.lean joins this list with those of other files. -/
def Rounds.names : List String := ["internal-batching-bare"]

/-! ## The ten routines

A prover's message can be filled by several calls of trRead, possibly from several callers. The call
that draws ends it. Each draw names its round. closeAs and the channel compare the name and the
numbers that the call gives with the plan's next entry. These are public conditions. All but the one
on the number of combined rows are already tested in the dry run; the channel compares that number
on a view. -/

/-- Receives n more elements and appends them to a. -/
def trReadLoop : Nat → Array E → Blk (Array E)
  | 0, a => pure a
  | n + 1, a => do
    let x ← Blk.recvE
    trReadLoop n (a.push x)

/-- Takes the next n items of the open message, which must be elements of the extension field. -/
def trRead (n : Nat) : Blk (Array E) := trReadLoop n (Array.emptyWithCapacity n)

/-- Takes the next item of the open message as the sum of a hiding polynomial. It must be the last
item of its message, and trAnswer .pscEpsilon must close that message: a prover that knew the drawn
element before it fixed the sum could fit the sum to a false claim. This function checks neither.
The C++ channel ends the program if trSum is not the last call before the draw of the name
pscEpsilon. That guards against a fault in the verifier's own code and is not reproduced here; the
strict reader only checks that the last item of such a round is a field element. -/
def trSum : Blk E := Blk.recvE

/-- Ends the open message and returns the one element that the verifier drew. -/
def trAnswer (r : RoundName) : Blk E := do
  noBatching r
  oneOf (← closeAs r.name (if r == .pscEpsilon then .join else .elems) 1 0 0)

/-- Ends the open message and returns the one element that the verifier drew by the rule that never
gives 0. In the dry run it is 0, as every value is. -/
def trAnswerNotZero (r : RoundName) : Blk E := do
  noBatching r
  oneOf (← closeAs r.name .elems 1 1 0)

/-- Ends the open message and returns the drawn matrix of the smallness test, column by column. Its
entries are -1, 0 or 1, and a column has one entry for each combination. The product of columns and
combinations is compared with the plan's entry. The number of combinations by itself, from which the
round's error is computed, is not. The C++ plan also says how many combinations the matrix has, and
the C++ channel compares that number. The plan's entry in the format has the number of the matrix's
entries and not this number. Fails if combinations is 0. -/
def trTrits (columns combinations : Nat) : Blk (Array Int) := do
  Blk.must (combinations != 0)
  pure (← closeAs rngName .entries 0 0 (columns * combinations)).trits.toArray

/-- Ends the open message in a round in which nothing is drawn. -/
def trEmpty (r : RoundName) : Blk Unit := do
  let _ ← closeAs r.name .nothing 0 0 0

/-- Ends the open message and returns the n elements that the verifier drew. -/
def trPoint (r : RoundName) (n : Nat) : Blk (Array E) := do
  noBatching r
  pure ((← closeAs r.name .elems n 0 0).elems.map E.ofTriple).toArray

/-- Draws the element that combines rows into one row, for a caller that learns the number of rows
only later. The caller must call trBatchRows afterwards: where the plan's entry counts rows, the
channel does not close the next round before the number has been compared. -/
def trBatchOpen : Blk E := do
  oneOf (← closeAs RoundName.batSigma.name .elems 1 0 0)

/-- Compares the number of rows that the element of trBatchOpen has combined with the plan's
entry. -/
def trBatchRows (rows : Nat) : Blk Unit := Blk.requireRows rows

/-- Draws the element x that combines rows into one row and returns its powers from 1 to
x^(rows - 1), the factor of each row. The number of rows must be the number in the plan's entry,
from which the round's error was computed. The caller gets the powers and not x: there are as many
factors as the plan counts rows, so a caller that gives each row a factor of its own combines no
more rows than that. Fails if rows is 0. -/
def trBatch (rows : Nat) : Blk (Array E) := do
  mustAs "internal-batching-bare" (rows != 0)
  let x ← trBatchOpen
  trBatchRows rows
  pure (powers x rows)

/-! ## The rounds of a sumcheck

This part holds what the rounds of all sumchecks share (vf_sumcheck_receive.h). The end values of a
sumcheck are the values, at the point of its challenges, of the functions that its summand is made
of. Where the prover sends them, an extra round in one more variable comes before them. How a
round's polynomial is summed, and the step that carries a running claim over a round, need the state
of a sumcheck and are defined with it (OnBytes/Model/Psc.lean). -/

/-- The five forms of a round of a sumcheck. In a round the prover sends a polynomial g in one
variable, and the claim c that is open before the round fixes one value: either g(0) + g(1) = c, or
(1 - z) g(0) + z g(1) = c for a known z. That equation determines one coefficient of g, which is
therefore not sent: the linear one under the first equation, the constant one under the second. The
others are sent lowest degree first. So a round tests no equation: the verifier computes the
coefficient that is not sent (OnBytes/Model/Psc.lean). -/
inductive RoundForm where
  /-- g has degree 2 and is summed with the weights 1 - z and z -/
  | eq2
  /-- g has degree 2, with g(0) + g(1) = c -/
  | sum2
  /-- g has degree 3, with g(0) + g(1) = c -/
  | sum3
  /-- g has a degree that the caller gives, with g(0) + g(1) = c (the name is the C++ program's) -/
  | nodes
  /-- g has a degree that the caller gives and is summed with the weights 1 - z and z -/
  | eq
  deriving DecidableEq, Repr, Inhabited

/-- The number of elements that a round of this form sends. degree is used only for nodes and
eq. -/
def roundValues (form : RoundForm) (degree : Nat := 0) : Nat :=
  match form with
  | .sum3 => 3
  | .nodes => degree
  | .eq => degree
  | .eq2 => 2
  | .sum2 => 2

/-- The number of scalars that a whole sumcheck sends if all its rounds have one form: 1 for the
hiding polynomial's sum, roundValues for each round, degreeInY coefficients of the extra round over
the end values, and the end values themselves (ends). degreeInY is meant to be 0 exactly if ends is
0, which is not tested here. Each scalar that a sub-proof sends has a number, its slot
(OnBytes/Model/Hide.lean). -/
def sumcheckSlots (form : RoundForm) (rounds ends degreeInY : Nat) (degree : Nat := 0) : Nat :=
  1 + rounds * roundValues form degree + degreeInY + ends

/-- The number of scalars that a whole sumcheck sends (compare sumcheckSlots) if its rounds have the
form nodes or eq and their degrees differ. degree: the degree of each round. -/
def sumcheckSlotsDegrees (degree : List Nat) (ends degreeInY : Nat) : Nat :=
  degree.foldl (· + ·) (1 + degreeInY + ends)

/-- The number of scalars that the sumcheck of one layer of a product tree with mu variables sends
(sumcheckSlots). Its rounds have the form eq2, and it ends in two values whose product is the
summand. -/
def layerSlots (mu : Nat) : Nat := sumcheckSlots .eq2 mu 2 2

/-- True for the two forms that sum under a factor of the equality polynomial. -/
def RoundForm.equality : RoundForm → Bool
  | .eq2 => true
  | .eq => true
  | _ => false

/-- True if the degree is one that the form admits: 1 to 64 for nodes and eq; any degree for the
other three. -/
def RoundForm.degreeOK (form : RoundForm) (degree : Nat) : Bool :=
  !(form == .nodes || form == .eq) || (decide (1 ≤ degree) && decide (degree ≤ 64))

/-- The challenge of a round of a sumcheck. -/
def roundDraw : Blk E := trAnswer .pscRound

end OnBytes.Model
