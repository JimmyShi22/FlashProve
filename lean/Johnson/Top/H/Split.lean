-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Split.lean: the kind of block SPLIT (one round: a row on two groups of oracle messages
becomes a row on each) as a value of `Kind` (Johnson/Top/Kind.lean), at any written list of sizes,
with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Split.lean. A size is that file's record `Size
E`: the library's record of a split with its type of cores. The joints hang on the size alone.
Main names:
  `kSplit L`: the kind.
  `kSplit_know`, `_point`, `_local`, `_onOut`, `_good`: without any premise.
  `HSplit`: closed, over the field `Cb.Gl.E`: for every list of sizes the kind is knowledge sound.
    `hSplit`: it holds.
Limits: no list of sizes is written here: the values at which a description of the programs'
protocol has such a block are built nowhere. Nothing says that a block of the kind is the step
that the programs run. Nothing on an honest prover.
-/
import Johnson.Top.Kind
import Cb.Pv.Split
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR

section
variable {E : Type} [Field E] [Fintype E]

/-- SPLIT, at a written list of sizes. -/
@[reducible] def kSplit (L : List (Cb.Pv.Split.Size E)) : Kind.{1} where
  Size := Cb.Pv.Split.Size E
  sizes := L
  src := fun s => jOf (Cb.Pv.Split.inJ s)
  dst := fun s => jOf (Cb.Pv.Split.outJ s)
  block := fun s => ⟨Cb.Pv.Split.R s, fun _ _ w => w, Cb.Pv.Split.eps s⟩

variable (L : List (Cb.Pv.Split.Size E))

theorem kSplit_know : (kSplit L).Know := fun s _ => Cb.Pv.Split.hAt s

theorem kSplit_point : (kSplit L).Point := fun s _ => Cb.Pv.Split.point s

theorem kSplit_local : (kSplit L).Local := fun s _ => Cb.Pv.Split.isLocal s

theorem kSplit_onOut : (kSplit L).OnOut := fun s _ a τ b hb ha => Cb.Pv.Split.onOut s a τ b ha hb

theorem kSplit_good : ∀ s ∈ L, ((kSplit L).block s).Good :=
  Kind.good (kSplit_know L) (kSplit_point L) (kSplit_local L) (kSplit_onOut L)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes. -/
def HSplit : Prop := ∀ L : List (Cb.Pv.Split.Size Cb.Gl.E), (kSplit L).Know

theorem hSplit : HSplit := kSplit_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hSplit
#print axioms VerifiableInference.OnPublicFiles.kSplit_good
