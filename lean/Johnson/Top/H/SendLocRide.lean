-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/SendLocRide.lean: the kind of block "SEND seed, LOC" whose first message bears a rider
(two rounds: a family of oracle messages and, beside them, an oracle without a sample, the fresh
mask of the new group's fold, are sent and answered by a joint seed; the answers are sent and
answered by long positions of the open word of the group before, which are read) as a value of
`Kind` (Johnson/Top/Kind.lean), at any written list of sizes, with the kind's hypothesis and the
three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Switch/SendLocRide.lean. A size is that file's
record
`Size E`. The joints hang on the size alone. They are the library's stages' joints, whose condition
is met by all statements (`IOR.Rels.cf`); the joint behind is read on the first component of the
oracles and asks nothing of the rider.
Main names:
  `kSendLocRide L`: the kind.
  `kSendLocRide_know`, `_point`, `_local`, `_onOut`, `_good`: under the condition
    `Cb.Pv.SendLocRide.OK` at every size of the list.
  `HSendLocRide`: closed, over the field `Cb.Gl.E`: for every list of sizes that meet the condition
    the kind is knowledge sound. `hSendLocRide`: it holds.
Limits: no list of sizes is written here: the values at which a description of the programs'
protocol has such a block are built nowhere, so the condition is proved of no value. Nothing
says that a block of the kind is the step that the programs run, or that its errors are small.
Nothing on an honest prover.
-/
import Johnson.Top.Kind
import Cb.Pv.Switch.SendLocRide
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- "SEND seed, LOC" with a rider, at a written list of sizes. -/
@[reducible] noncomputable def kSendLocRide (L : List (Cb.Pv.SendLocRide.Size E)) : Kind.{1} where
  Size := Cb.Pv.SendLocRide.Size E
  sizes := L
  src := fun s => jOf (Cb.Pv.SendLocRide.inJ s)
  dst := fun s => jOf (Cb.Pv.SendLocRide.outJ s)
  block := fun s => ⟨Cb.Pv.SendLocRide.R s, Cb.Pv.SendLocRide.ext s, Cb.Pv.SendLocRide.eps s⟩

variable (L : List (Cb.Pv.SendLocRide.Size E)) (h : ∀ s ∈ L, Cb.Pv.SendLocRide.OK s)
include h

theorem kSendLocRide_know : (kSendLocRide L).Know := fun s hs => Cb.Pv.SendLocRide.hAt s (h s hs)

theorem kSendLocRide_point : (kSendLocRide L).Point := fun s hs => Cb.Pv.SendLocRide.point s (h s
  hs)

theorem kSendLocRide_local : (kSendLocRide L).Local := fun s hs => Cb.Pv.SendLocRide.isLocal s (h s
  hs)

theorem kSendLocRide_onOut : (kSendLocRide L).OnOut :=
  fun s hs a τ b hb ha => Cb.Pv.SendLocRide.onOut s (h s hs) a τ b ha hb

theorem kSendLocRide_good : ∀ s ∈ L, ((kSendLocRide L).block s).Good :=
  Kind.good (kSendLocRide_know L h) (kSendLocRide_point L h) (kSendLocRide_local L h)
      (kSendLocRide_onOut L h)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes that meet
the condition. -/
def HSendLocRide : Prop :=
  ∀ L : List (Cb.Pv.SendLocRide.Size Cb.Gl.E), (∀ s ∈ L, Cb.Pv.SendLocRide.OK s) → (kSendLocRide
      L).Know

theorem hSendLocRide : HSendLocRide := kSendLocRide_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hSendLocRide
#print axioms VerifiableInference.OnPublicFiles.kSendLocRide_good
