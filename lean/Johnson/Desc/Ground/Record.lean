-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Record.lean: the plain functions of Johnson/Desc/First/Base/Ground.lean as a
value of the record of seven ground functions over which a chain's steps and a sending are written
(Desc.Plain.Ground, Johnson/Desc/Ground/Calls.lean).

This file holds one definition; no theorem is stated. Of a GPar one field is read by one function:
recv reads firstTree. Calls.lean has a definition of the same short name, groundG, with the same
seven fields, in the namespace Desc.Plain; no theorem ties the two.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Ground.Calls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground

/-- The seven ground functions := the plain effects. -/
def groundG {L : Type} : Desc.Plain.Ground L :=
  { newGroup := fun _ => newGroupP, recv := fun p => recvP p.firstTree, admit := fun _ => admitP,
    join := fun _ => joinP, addRow := fun _ => addRowP, addRows := fun _ => addRowsP,
    takeMask := fun _ => takeMaskP }

end VerifiableInference.Desc.Ground
