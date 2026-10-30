-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkSched.lean: tests on a planner's answer p that the steps of the description of
the proof file's shared chain make on the public half of the state that they carry, as far as
functions of the library say them at terms of the plan. Definitions with code alone; no theorem.

Main names (namespace VerifiableInference.OnPublicFiles.OkD):
  padsU, padsO: at each of the chain's two sendings padMade (Johnson/Desc/Own/Send.lean) returns at
    every notice that has answers. A step asks it of the shape in the statement's entry for the
    message.
  free: where the shared tree needs a split, the split's message has a free mask entry
    (Send.freeMaskEntries). A step asks it of the ledger in that entry, before any entry is taken.
  sched p: **the test**: the three.

It reads the plan alone and names no size. THESE ARE NOT ALL: the other tests on the public half
of the carried state (joinings, sizes of lists, marks, Omega alone in its tree) stand in the steps.

What is not claimed. THAT ANY OF THEM SAYS YES AT ANY p: nothing is evaluated here. THAT A STEP's
TEST ON THE STATE IS THE TEST HERE: no law says that the shape or the ledger in the state is the
plan's.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.OnPlan.OkDesc
import Johnson.Desc.Own.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

/-- Every notice that has answers has room for its pad. -/
def padsOk (codes : Codes) (sent : Array OracleNotice) : Bool :=
  sent.all fun n =>
    n.shape.answers == 0 || (VerifiableInference.Desc.Own.padMade codes n.shape).isSome

/-- At the sending of the folded row. -/
def padsU (p : Model.Verify.Planned) : Bool := padsOk (codesS p) (sentU p)

/-- At the sending of Omega. -/
def padsO (p : Model.Verify.Planned) : Bool := padsOk (codesS p) (sentO p)

/-- Where the shared tree needs a split, the split's message has a free mask entry. -/
def free (p : Model.Verify.Planned) : Bool :=
  !(linS p).sharedSplitNeeded ||
    decide (0 < Send.freeMaskEntries (linS p).sharedSplit.maskRows
      ((codesS p).mask.getD (linS p).sharedSplit.maskCode default).ell
      (linS p).sharedSplit.answers)

/-- **The test on the public half of the carried state, as far as it is said at the plan.** -/
def sched (p : Model.Verify.Planned) : Bool := padsU p && padsO p && free p

end VerifiableInference.OnPublicFiles.OkD
