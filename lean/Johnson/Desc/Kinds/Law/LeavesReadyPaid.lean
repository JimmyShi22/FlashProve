-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LeavesReadyPaid.lean: LeavesReady (Law/SilentPlanes.lean: what the lookup's
run "planes" and the head's run "join" ask of what the lookup heard and of the ledger), PAID FROM
THE LOOKUP's SHARP ITEM "left" (Johnson/Desc/First/Look/K3LeftItem.lean: k3LeftItem): and with it
that the slot of the bits' value is filled. Two theorems; both are calls of
Johnson/Top/H/Keep/K3LeftWindow.lean (leavesReady_of_leftAt · leftAt_numbers), which writes
LeavesReady's five clauses out in their order.

  leavesReady_at    at K3LeftAt, general in the readers of the ledger and of what was heard.
  leavesReady_item  at the item, at a verifier's state.

WHAT IT IS NOT. Implications: the item is a premise (it stands in the promise at the border in front
of the output head's own sub-protocol). THAT THE SLOTS OF THE STARTING FORM OF THE SUMCHECK OVER THE
LEAVES ARE FILLED IS NOT HERE: the item does not say it (K3LeftWindow.lean's LeavesFilled: a fact
along the fold). Nothing on soundness.
LETTERS. F', g stand under "there is": tied by the two readers' answers at s.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SilentPlanes
import Johnson.Top.H.Keep.K3LeftWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles (K3LeftAt LeftQ leavesReady_of_leftAt leftAt_numbers)

/-- **At K3LeftAt.** -/
theorem leavesReady_at {T : Type} {fork : T → Option Fork}
    {heard : T → Option OnBytes.Model.Forest.Heard} {h : OnBytes.Model.Forest.Shape}
    {lm first n : Nat} {s : T} (L : K3LeftAt fork heard h lm first (LeftQ n) s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧ LeavesReady g F' ∧
      OnBytes.PscRun.Filled F' g.sBit := by
  obtain ⟨F', g, a, b, c⟩ := leavesReady_of_leftAt L
  obtain ⟨F2, g2, a2, b2, _, _, _, _, _, _, _, _, _, hB⟩ := leftAt_numbers L
  obtain rfl : F' = F2 := Option.some.inj (a.symm.trans a2)
  obtain rfl : g = g2 := Option.some.inj (b.symm.trans b2)
  exact ⟨F', g, a, b, ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1, c.2.2.2.2⟩, hB⟩

/-- **At the item.** -/
theorem leavesReady_item {p : First.Look.P} {s : S}
    (L : VerifiableInference.OnPublicFiles.k3LeftItem p s) :
    ∃ F' g, s.fork? = some F' ∧ s.lookHeard? = some g ∧ LeavesReady g F' ∧
      OnBytes.PscRun.Filled F' g.sBit := by
  obtain ⟨⟨h, _, L⟩, _⟩ := L
  exact leavesReady_at L

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.leavesReady_item
