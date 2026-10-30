-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/ReplyBlock.lean: THE NEXT TOKEN as a kind of block (Johnson/Desc/Block.lean):
ReplyKind.lean's pieces in the record's nine fields. The comparison with the client's token is no
part of the block: it is the file's last test (the kind's own form of it: Reply.fin; the proof
file's description asks S.finAsked, Johnson/Desc/First/State.lean). It shows nothing by itself.
Definitions with code; no theorem.

-/
import Johnson.Desc.Block
import Johnson.Desc.Kinds.ReplyKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Reply

/-- The kind. Its parameter: V, the number of vocabulary entries. It has no claims. That the plan
has just one entry named REPLY follows where the blocks' rounds in a row are held against the plan's
entries, if this kind stands at one place. -/
def kind {S Cl : Type} (L : Seat S) (link piece : Nat) : Kind Nat S Cl := fun V =>
  { name := "the next token"
    place := ⟨1, some link, piece, .K7⟩
    planOk := 2 ≤ V
    rounds := rounds
    oracles := [[]]
    before := []
    decide := fun s rs _ => decideE V L s rs
    claims := []
    after := [] }

end VerifiableInference.Desc.Kinds.Reply
