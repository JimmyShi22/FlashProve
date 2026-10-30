-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/SendL8.lean: THE PLAIN SENDING IN THE PLACE THAT THE SWITCH's ROW KEEPS FOR IT
(SendFn, K2/Step.lean): sendOpen: the program's flag ownRound := false: it asks that nothing
is owed from the round closed before, the first entry's name | drawNZ | rows = 0 and that round 1
draws what the entry says; reads the answers as round 2's first items; asks nothing of round 2's
draws; hands back
the messages' numbers, how many items it took, and the state: at the value groundG of the seven
ground functions: plain functions on data.
The fifth argument of SendFn («settled») goes to sendOpen's «owed»: none where nothing waits, some 1
else (the row asks it itself too, a line earlier: [S4], K2/Step.lean).
An adapter: it lays the arguments into the plain ground's state record at Unit and reads the result
back. No Blk, no Ctx. No soundness: definitions with code.
-/
import Johnson.Top.H0.Tw.K2.Step
import Johnson.Desc.Sending.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

def sendByL8 : SendFn := fun P S B roots settled notices rS rL =>
  match VerifiableInference.Desc.First.Send.sendOpen (Desc.Plain.groundG : Desc.Plain.Ground Unit)
      ⟨P.samples, P.firstTree⟩ (if settled then none else some 1) notices P.eSeed
      ⟨S, B, roots, [], ()⟩ rS rL with
  | some (ids, took, d) => .ok ⟨d.st, d.book, d.roots, ids, took⟩
  | none => .error "L8: the sending refuses"

end Tw.K2
