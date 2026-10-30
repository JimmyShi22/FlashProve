-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Loc.lean: the kind of block LOC on a group (one round: the verifier draws long
positions of an open word and reads them) as a value of `Kind` (Johnson/Top/Kind.lean), at any
written list of sizes, with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Loc.lean. A size is that file's record `Size
E`: the library's record of the locations with its type of cores. The joints hang on the size alone.
Main names:
  `kLoc L`: the kind.
  `kLoc_know`, `_point`, `_local`, `_onOut`, `_good`: under the condition `Cb.Pv.Loc.OK` at every
    size of the list.
  `HLoc`: closed, over the field `Cb.Gl.E`: for every list of sizes that meet the condition the kind
    is knowledge sound. `hLoc`: it holds.
Limits: the round of the same name in the test on a stored table is another kind
(Johnson/Top/H/Lin.lean). No list of sizes is written here: the values at which a description of the
programs' protocol has such a block are built nowhere, so the condition is proved of no value.
Nothing says that a block of the kind is the step that the programs run, or that its error is small.
Nothing on an honest prover.
-/
import Johnson.Top.Kind
import Cb.Pv.Loc
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- LOC on a group, at a written list of sizes. -/
@[reducible] noncomputable def kLoc (L : List (Cb.Pv.Loc.Size E)) : Kind.{1} where
  Size := Cb.Pv.Loc.Size E
  sizes := L
  src := fun s => jOf (Cb.Pv.Loc.inJ s)
  dst := fun s => jOf (Cb.Pv.Loc.outJ s)
  block := fun s => ⟨Cb.Pv.Loc.R s, fun _ _ w => w, Cb.Pv.Loc.eps s⟩

variable (L : List (Cb.Pv.Loc.Size E)) (h : ∀ s ∈ L, Cb.Pv.Loc.OK s)
include h

theorem kLoc_know : (kLoc L).Know := fun s hs => Cb.Pv.Loc.hAt s (h s hs)

theorem kLoc_point : (kLoc L).Point := fun s hs => Cb.Pv.Loc.point s (h s hs)

theorem kLoc_local : (kLoc L).Local := fun s hs => Cb.Pv.Loc.isLocal s (h s hs)

theorem kLoc_onOut : (kLoc L).OnOut :=
  fun s hs a τ b hb ha => Cb.Pv.Loc.onOut s (h s hs) a τ b ha hb

theorem kLoc_good : ∀ s ∈ L, ((kLoc L).block s).Good :=
  Kind.good (kLoc_know L h) (kLoc_point L h) (kLoc_local L h) (kLoc_onOut L h)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes that meet
the condition. -/
def HLoc : Prop :=
  ∀ L : List (Cb.Pv.Loc.Size Cb.Gl.E), (∀ s ∈ L, Cb.Pv.Loc.OK s) → (kLoc L).Know

theorem hLoc : HLoc := kLoc_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hLoc
#print axioms VerifiableInference.OnPublicFiles.kLoc_good
