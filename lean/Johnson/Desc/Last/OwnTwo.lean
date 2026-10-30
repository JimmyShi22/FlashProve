-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/OwnTwo.lean: A TEST WITH CODE ON THE FIRST CHAIN'S STATE: the own group that is
handed to the last chain has two members, and each of them has one sample row. One definition. THIN:
it imports Johnson/Desc/Third/Border.lean alone.

Why. Of the six tests that the door of the last chain asks of the first chain's last state
(`doorFirstL`, Johnson/Desc/Last/DoorTexts.lean) four ride in the first table's promise under names
of their own (tidy; the book fits; the weights; (Eval) laid). These are the other two, by
themselves, so that they can ride as one named item (Johnson/Desc/First/FillOwnTwo.lean) and be run
at a chain's borders.

Main name (namespace `VerifiableInference.Desc.Last`).
  **`ownTwoB s`**: where `firstOfS s` hands something: the group at the number that is handed as the
    own group's is there, has two members, and each member is a message that is there and has one
    sample row. Where nothing is handed: yes.

Limits. IT HAS RUN AT NO STATE. Idle at every border in front of the block that lays W's number. By
its text it can say yes, where something is handed, only at a plan with one answer to a sample and
without a split's message in the own group. Who earns and keeps it: nobody yet. Nothing on soundness
or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Third.Border

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third

/-- **The own group that is handed has two members, each with one sample row.** -/
def ownTwoB (s : First.S) : Bool :=
  match firstOfS s with
  | some f =>
    match f.st.groups[f.own]? with
    | some G => G.members.size == 2 && G.members.toList.all fun i =>
        match f.st.oracles[i]? with
        | some x => x.sampleRows.size == 1
        | none => false
    | none => false
  | none => true

end VerifiableInference.Desc.Last
