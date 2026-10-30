-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BehindLayersAtHead.lean: a link with an even number below 24 is of the sort
"layers": `sub_even`. One theorem. Nothing is evaluated.

  `sub_even`: g < 12 ⊢ subAt (2 * g) = .layers.

The sub-protocol "behind the batching" under the head at the twelve layers' links is stated in
SeatsNamed.lean (layers_named), with every step named and every parameter tied to a value.

The import lines say more than this one theorem needs: SeatsNamed.lean reaches modules through this
file; which of the three lines it needs was not sought.

Limits. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BehindAtHead
import Johnson.Desc.First.TailClaims.FreeSlotChain
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Block Chain Link Place KindName Claim seatSame)
open VerifiableInference.Desc.First (S ModelPart K8.ParW)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law.Tests
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T fullLinks)

theorem sub_even (g : Nat) (hg : g < 12) : subAt (2 * g) = .layers := by
  unfold subAt
  rw [if_neg (by omega), if_pos (by omega)]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sub_even
