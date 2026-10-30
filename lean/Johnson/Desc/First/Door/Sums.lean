-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Door/Sums.lean: DEFINITIONS WITH CODE; NO THEOREM: the tests on a link's sums:
what is asked of the link's ledger behind its last equation and in front of its closing.

A link adds its equations up under powers of its batching element. The ledger (`Fork`, the program's
own plain record) then holds, for each scalar that the prover has sent, its coefficient in the one
equation, and for each committed array the weights of its entries. Two tests read these sums. Each
is a RUN OF THE SECOND SORT: from the ledger to a refusal or to the ledger handed on; they stand in
the link's order like the claims.

Main names:
  `freeSlotOk n merge F`: every sent scalar stands in a claim: for each of the link's first n slots
    the coefficient is other than 0; but at the slot of the merge's end value, if the link has one,
    it is 0: no equation of this link says what that value is; the row on the committed weights
    does.
  `freeSlotRun`: the same as a run; the ledger is handed on as it came.
  `weightsRun nU tl`: the smallness test's tests on the sampled weights, with the rows' weights set
    between them:
    `testsP` (Johnson/Desc/First/TailClaims/SelfRows.lean), by name.
  `freeSlotE`, `weightsE`: the same two with the name of the guard that refused.

What kind of tests these are. A coefficient is a sum of products of drawn elements (at a layers'
link also of values that the prover has sent): an unlucky challenge can make it 0: the run is
refused then too. By `verify-on-bytes`'s comments (OnBytes/Model/Head.lean:265-268) the first "must
stay: a value that the prover sends and that no claim names would be bound by no equation, and no
verifier would notice".

`verify-on-bytes` asks the first test in three places, in three forms: Layer.freeSlotTest
(Layer.lean:513-516: it marks and goes on), Attention.noFreeSlot (Attention.lean:144-146: no merge),
the first line of Head.selfTests (Head.lean:272-273). SumsLaw.lean says that their three conditions
are `freeSlotOk`.
Limits: definitions alone. n and merge are the plan's: who hands them in is the link's text.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.TailClaims.SelfRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Door
open OnBytes OnBytes.Model

/-- Every sent scalar stands in a claim. n: the number of the link's slots that messages fill.
merge: the slot of the merge's end value, if the link has one. -/
def freeSlotOk (n : Nat) (merge : Option Nat) (F : Fork) : Bool :=
  (List.range n).all fun j => isZeroE (F.LS.getD j zeroE) == (merge == some j)

/-- The same with a name for the refusal. -/
def freeSlotE (n : Nat) (merge : Option Nat) (F : Fork) : Except String Fork :=
  if freeSlotOk n merge F then .ok F else .error "free-slot"

/-- The same as a run of the second sort. -/
def freeSlotRun (n : Nat) (merge : Option Nat) (F : Fork) : Option Fork :=
  (freeSlotE n merge F).toOption

/-- The tests on the sampled weights, with the rows' weights set between them; a refusal bears its
guard's name. -/
def weightsE (nU : Array Nat) (tl : HTailF2) (F : Fork) : Except String Fork :=
  TailClaims.testsP nU tl F

/-- The same as a run of the second sort. -/
def weightsRun (nU : Array Nat) (tl : HTailF2) (F : Fork) : Option Fork :=
  (weightsE nU tl F).toOption

end VerifiableInference.Desc.First.Door
