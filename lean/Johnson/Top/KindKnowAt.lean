-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/KindKnowAt.lean: a kind of block at the base whose every size has `TWhole.KnowAt` has
its hypothesis and its three side facts.

`TWhole.KnowAt R A B ext ε` (Cb/G6/Cut.lean) has four fields: point queries, a local verifier, the
condition carried, and knowledge soundness for every tuple of committed messages. These are, field
by field, the four propositions of a `BaseKind` (Johnson/Top/Kind.lean). Nothing new is proved:
four projections and `BaseKind.good`.
Main names:
  `BaseKind.KnowAtAll`: every block of the kind has `KnowAt`, at the signature's messages.
  `BaseKind.know_of_knowAt`, `point_of_knowAt`, `local_of_knowAt`, `onOut_of_knowAt`.
  `BaseKind.good_of_knowAt`: every block of the lifted kind has `KObj.BK.Good`.
  `BaseKind.knowAtAll_iff`: and back.
Limits: it says nothing on whether a kind's block is the step that the programs run.

-/
import Johnson.Top.Kind
import Cb.G6.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

universe u

namespace BaseKind
variable {E : Type} [Field E] (β : BaseKind.{u} E)

/-- Every block of the kind has the common goods' KnowAt, at the signature's messages. -/
def KnowAtAll : Prop :=
  ∀ s ∈ β.sizes, TWhole.KnowAt (β.R s) (β.A s) (β.B s) (β.ext s) (β.ε s)

variable {β}

theorem know_of_knowAt (h : β.KnowAtAll) : β.Know := fun s hs => (h s hs).know
theorem point_of_knowAt (h : β.KnowAtAll) : β.Point := fun s hs => (h s hs).point
theorem local_of_knowAt (h : β.KnowAtAll) : β.Local := fun s hs => (h s hs).isLocal
theorem onOut_of_knowAt (h : β.KnowAtAll) : β.OnOut := fun s hs => (h s hs).onOut

/-- KnowAt at every size: every block of the lifted kind has the spine's property. -/
theorem good_of_knowAt (h : β.KnowAtAll) : ∀ s ∈ β.sizes, (β.toKind.block s).Good :=
  good (know_of_knowAt h) (point_of_knowAt h) (local_of_knowAt h) (onOut_of_knowAt h)

/-- And back: the four are KnowAt. -/
theorem knowAtAll_iff : β.KnowAtAll ↔ β.Know ∧ β.Point ∧ β.Local ∧ β.OnOut :=
  ⟨fun h => ⟨know_of_knowAt h, point_of_knowAt h, local_of_knowAt h, onOut_of_knowAt h⟩,
    fun h s hs => ⟨h.2.1 s hs, h.2.2.1 s hs, h.2.2.2 s hs, h.1 s hs⟩⟩

end BaseKind

#print axioms VerifiableInference.OnPublicFiles.BaseKind.good_of_knowAt
#print axioms VerifiableInference.OnPublicFiles.BaseKind.knowAtAll_iff

end VerifiableInference.OnPublicFiles
