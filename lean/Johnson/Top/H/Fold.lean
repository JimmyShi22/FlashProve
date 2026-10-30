-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Fold.lean: the kind of block FOLD as a value of `Kind` (Johnson/Top/Kind.lean), at any
written list of sizes, in its two forms, with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Tower/Fold.lean. A size is that file's record
`FoldSize E`: data alone. The joints hang on the size alone.
Main names:
  `kFoldOwn L`, `kFoldRide L`: the kinds: the fold that sends its fresh mask in its first round; the
    fold whose mask was sent earlier and stands among the input's oracles.
  `kFoldOwn_know`, `_point`, `_local`, `_onOut`, `_good` and the same for `kFoldRide`: under the
    conditions at every size of the list (`FoldSize.OK`); `_point` and `_onOut` without.
  `HFoldOwn`, `HFoldRide`: closed, over the field `Cb.Gl.E`: for every list of sizes that meet the
    conditions the kind is knowledge sound. `hFoldOwn`, `hFoldRide`: they hold.
Limits: no list of sizes is written here. Values of Y at stages of a proximity test that are given
in numbers, the conditions at these values, and written lists of such numbers, meant as a key
file's: Johnson/Top/H/FoldValues.lean and Johnson/Top/H/KeyValues.lean, with limits of their own.
Nothing says that a block of the kind is the step that the programs run, or that its errors are
small. The extractor's value where a transcript has no image (nowhere) is 0. Nothing on an honest
prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Tower.Fold
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv.Tower

section
variable {E : Type} [Field E] [Fintype E]

/-- FOLD with its own mask, at a written list of sizes. -/
@[reducible] noncomputable def kFoldOwn (L : List (FoldSize E)) : Kind.{1} where
  Size := FoldSize E
  sizes := L
  src := fun s => jOf (inOwn s.Y s.e)
  dst := fun s => jOf (outJ s.Y s.e)
  block := fun s =>
    ⟨foldOwn s.Y s.fx, extOwn s.Y s.fx s.d 0, errOwn s.Y s.fx s.Lst s.mC s.mS s.mW⟩

/-- FOLD whose mask was sent earlier, at a written list of sizes. -/
@[reducible] noncomputable def kFoldRide (L : List (FoldSize E)) : Kind.{1} where
  Size := FoldSize E
  sizes := L
  src := fun s => jOf (inRide s.Y s.e)
  dst := fun s => jOf (outJ s.Y s.e)
  block := fun s =>
    ⟨foldRide s.Y s.fx, extRide s.Y s.fx s.d 0, errRide s.Y s.fx s.Lst s.mC s.mS s.mW⟩

variable (L : List (FoldSize E))

theorem kFoldOwn_know (h : ∀ s ∈ L, s.OK) : (kFoldOwn L).Know := fun s hs => s.hOwn (h s hs) 0

theorem kFoldOwn_point : (kFoldOwn L).Point := fun s _ => foldOwn_point s.Y s.fx

theorem kFoldOwn_local (h : ∀ s ∈ L, s.OK) : (kFoldOwn L).Local := fun s hs =>
  foldOwn_local s.Y s.fx (h s hs).codes.1.1 (h s hs).codes.1.2.1 (h s hs).codes.1.2.2

theorem kFoldOwn_onOut : (kFoldOwn L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kFoldOwn_good (h : ∀ s ∈ L, s.OK) : ∀ s ∈ L, ((kFoldOwn L).block s).Good :=
  Kind.good (kFoldOwn_know L h) (kFoldOwn_point L) (kFoldOwn_local L h) (kFoldOwn_onOut L)

theorem kFoldRide_know (h : ∀ s ∈ L, s.OK) : (kFoldRide L).Know := fun s hs => s.hRide (h s hs) 0

theorem kFoldRide_point : (kFoldRide L).Point := fun s _ => foldRide_point s.Y s.fx

theorem kFoldRide_local (h : ∀ s ∈ L, s.OK) : (kFoldRide L).Local := fun s hs =>
  foldRide_local s.Y s.fx (h s hs).codes.1.1 (h s hs).codes.1.2.1 (h s hs).codes.1.2.2

theorem kFoldRide_onOut : (kFoldRide L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kFoldRide_good (h : ∀ s ∈ L, s.OK) : ∀ s ∈ L, ((kFoldRide L).block s).Good :=
  Kind.good (kFoldRide_know L h) (kFoldRide_point L) (kFoldRide_local L h) (kFoldRide_onOut L)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes that meet
the conditions. -/
def HFoldOwn : Prop := ∀ L : List (FoldSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kFoldOwn L).Know

theorem hFoldOwn : HFoldOwn := kFoldOwn_know

/-- The same for the fold whose mask was sent earlier. -/
def HFoldRide : Prop := ∀ L : List (FoldSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kFoldRide L).Know

theorem hFoldRide : HFoldRide := kFoldRide_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hFoldOwn
#print axioms VerifiableInference.OnPublicFiles.hFoldRide
#print axioms VerifiableInference.OnPublicFiles.kFoldOwn_good
#print axioms VerifiableInference.OnPublicFiles.kFoldRide_good
