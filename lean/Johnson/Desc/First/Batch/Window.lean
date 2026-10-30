-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Window.lean (kind K9's place): DEFINITIONS WITH CODE; NO THEOREM: A WINDOW
OF SLOTS IS ITS OWNERS' ALONE.
Some blocks hide values of their own under a stretch of a segment's slots (the smallness test: the
slots from slotA up to slotB). Only the claims of that block's own runs may name such a slot: a
weight that another run's claim laid there would be added to the coefficient under which the
block's own equations are later read off the ledger.
The program `verify-on-bytes` asks this twice IN TIME: no weight lies on the window in front of the
block's own claims (OnBytes/Model/Tail.lean:1047), and behind them the weights stay as left (:1155).
Where a step's claims are all made first and then added, such tests in time compare the window with
itself. So it is asked WHERE THE CLAIMS ARE GATHERED, of each run's list, by the run's name.
  Window          the owners; the slots first ≤ j < behind. AN OWNER IS A RUN AS THE SEGMENT's ORDER
                  NAMES IT: (the block's number, the run's name): two blocks of one kind state runs
                  of one name (the lookup on the calls and the lookup on the digits both have
                  "objects"): the bare name could not tell them apart.
  windowsOk ws run cls   a run that is not among a window's owners names no slot of it: else
                  "K9.window". A slot is named where it stands in a claim's form, whatever its
                  coefficient.
WHO CALLS IT: the gathering of a step of adding, behind each run, AT EVERY STEP OF THE SEGMENT, with
the same windows.
Compiled; run nowhere.

-/
import Johnson.Desc.First.Batch.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- A stretch of slots that the runs named here state as their own. -/
structure Window where
  /-- the runs that may name its slots: the block's number in the segment's order, the run's name -/
  owners : List (Nat × String)
  /-- its first slot -/
  first : Nat
  /-- the slot behind its last -/
  behind : Nat

/-- Slot j lies in the window. -/
def Window.holds (w : Window) (j : Nat) : Bool := decide (w.first ≤ j) && decide (j < w.behind)

/-- The claim's form names a slot of the window. -/
def Window.namedBy (w : Window) (cl : Claim) : Bool := cl.form.slots.any fun x => w.holds x.1

/-- **A run's claims against the windows.** -/
def windowsOk (ws : List Window) (run : Nat × String) (cls : List Claim) : Ans Unit :=
  ws.forM fun w => need "K9.window" (w.owners.contains run || !cls.any w.namedBy)

end VerifiableInference.Desc.K9
