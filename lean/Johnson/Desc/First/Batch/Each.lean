-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Each.lean (kind K9's place): DEFINITIONS WITH CODE; NO THEOREM: THE TEST
BEHIND EACH RUN OF A SEGMENT's CLAIMS: what a segment (Johnson/Desc/Block.lean: Link) lays in its
field `each`.
The batching is handed the segment's claims as one function, which calls the hearing kinds' named
runs in the segment's order and joins their lists: K9 sees one list. Two things can be asked only of
ONE RUN's OWN LIST, BY THE RUN's NAME; the gatherer asks them behind each run:
  (1) A WINDOW OF SLOTS IS ITS OWNERS' ALONE (Johnson/Desc/First/Batch/Window.lean: windowsOk): a
      run that is not among a window's owners names no slot of it: "K9.window".
  (2) A RUN LAYS AS MANY CLAIMS AS IS DUE, where a number is due: under the name that comes with the
      number (the lookup on the digits lays as many claims as it has equations of its own:
      "K9.lookup-rows-counted").
GENERAL IN THE STATE: the windows and the due numbers are read off the record behind the run by two
functions that the segment's maker hands in.
  eachRun ws due run cls t
WHAT (1) IS FOR. The program `verify-on-bytes` has two tests in time (OnBytes/Model/Tail.lean:1047:
no weight lies on the window in front of its owners' claims; :1155: behind them the weights stay as
they were left). Where a whole segment's claims are made first and then added, such tests compare
the window with itself. (1) asks the same by name. INSIDE THE ADDING a coefficient of a slot is
written at one place alone, from a claim's form's slots (Johnson/Desc/First/Batch/Add.lean:
addForm), which are what windowsOk reads; an entry or a run of a claim writes arrays' weights alone.
"ONLY THE OWNERS' CLAIMS PUT A WEIGHT ON THE WINDOW" FOLLOWS ONLY WITH FOUR THINGS MORE, NONE OF
WHICH IS ASKED HERE: the ledger is empty at the draw ("K9.ledger-empty" asks that) · NOTHING BUT THE
ADDING WRITES THE SLOTS' COEFFICIENTS between the draw and the one equation (a run, or a step
between two addings, that wrote them itself would be seen by no test here; Tail.lean:1155 would
have seen it) · THE WINDOWS STAND STILL AND ARE THE REAL ONES (ws is read off the record behind each
run: a run that turned what ws reads would move the window; where ws gives no window the test is
idle and says yes) · EVERY CLAIM THAT IS ADDED HAS GONE THROUGH eachRun UNDER ITS TRUE PAIR (the
block's number, the run's name). No theorem says any of this yet.

-/
import Johnson.Desc.First.Batch.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

variable {T : Type}

/-- **The test behind a run.** ws: the windows. due: for a run, the name of the count and the number
of claims that it is to lay; nothing where none is due. run: the run as the segment's order names
it. cls: that run's own list. t: the record BEHIND the run: ws and due are both read there. -/
def eachRun (ws : T → List Window) (due : Nat × String → T → Option (String × Nat))
    (run : Nat × String) (cls : List Claim) (t : T) : Ans Unit := do
  windowsOk (ws t) run cls
  match due run t with
  | none => pure ()
  | some d => need d.1 (cls.length == d.2)

end VerifiableInference.Desc.K9
