-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeardName.lean: THE SMALL LAWS AT THE NAME S.heard (Johnson/Desc/First/
StateHeard.lean): HeardEntered.lean's laws, carried over by `heardA_eq : heardA = S.heard := rfl`.
BUILT OVER State.lean, StateOut.lean AND
StateHeard.lean.

-/
import Johnson.Desc.First.StateHeard
import Johnson.Desc.Kinds.Law.HeardEntered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

theorem heardA_eq : heardA = S.heard := rfl

/-- **(L2) at the name: K6's block at S.** -/
theorem blockAt_leaves_heard (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) :
    Leaves S.heard (blockAt h iU3 work l) := heardA_eq ▸ blockAt_leaves_heardA h iU3 work l

/-- The same for `blockOf`, the block as it rides. -/
theorem blockOf_leaves_heard (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit)
    (hb : blockOf W l = some b) : Leaves S.heard b := heardA_eq ▸ blockOf_leaves_heardA W l b hb

/-- **(L1) AS TYPED, at the name, for the next token's block under its wrapper: at every record.**
-/
theorem entered_lays (link piece V : Nat) :
    Lays S.heard replyOf (enteredCopy (Reply.kind k7SeatCopy link piece V)) :=
  heardA_eq ▸ entered_lays_A link piece V

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockOf_leaves_heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.entered_lays
