-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Stage.lean: the kind of block "one stage of a proximity test" (the fold's rounds, then
the two rounds of the code switch) as a value of `Kind` (Johnson/Top/Kind.lean), at any written list
of sizes, in its two forms, with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Tower/Stage.lean. A size is that file's record
`StageSize E`: data alone. The joints hang on the size alone.
Main names:
  `kStageOwn L`, `kStageRide L`: the kinds: the fold sends its fresh mask in its first round; the
    mask was sent earlier and stands among the input's oracles. In both the switch's first message
    bears a rider for a later block.
  `kStageOwn_know`, `_point`, `_local`, `_onOut`, `_good` and the same for `kStageRide`: `_know`
    under the conditions at every size of the list (`StageSize.OK`); `_local` under these,
    and if the new code's transformation reads what it declares (`StageSize.OKLocal`).
  `HStageOwn`, `HStageRide`: closed, over the field `Cb.Gl.E`: for every list of sizes that meet the
    conditions the kind is knowledge sound. `hStageOwn`, `hStageRide`: they hold.
Limits: no list of sizes is written here: the values of a stage's letters at which a description of
the programs' protocol has such a block are built nowhere, so the conditions are not stated at
them, clause by clause, and are proved of no value. Nothing says that a block of the kind is the
step that the programs run, or that its errors are small. The first stage of a test on a group of
oracle messages, with its arrangement of rows, is not treated. Nothing on an honest prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Tower.Stage
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv.Tower

section
variable {E : Type} [Field E] [Fintype E]

/-- A stage whose fold sends its mask, at a written list of sizes. -/
@[reducible] noncomputable def kStageOwn (L : List (StageSize E)) : Kind.{1} where
  Size := StageSize E
  sizes := L
  src := fun s => jOf (stageInOwn s.Y s.sl s.e)
  dst := fun s => jOf (stageOut s.Y s.sl s.e s.S s.Cw s.e')
  block := fun s =>
    ⟨stageOwn s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW,
      stageExtOwn s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.d s.e',
      stageErrOwn s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.Lst s.mC s.mS s.mW s.L⟩

/-- A stage whose fold's mask was sent earlier, at a written list of sizes. -/
@[reducible] noncomputable def kStageRide (L : List (StageSize E)) : Kind.{1} where
  Size := StageSize E
  sizes := L
  src := fun s => jOf (stageInRide s.Y s.sl s.e)
  dst := fun s => jOf (stageOut s.Y s.sl s.e s.S s.Cw s.e')
  block := fun s =>
    ⟨stageRide s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW,
      stageExtRide s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.d s.e',
      stageErrRide s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW s.Lst s.mC s.mS s.mW s.L⟩

variable (L : List (StageSize E))

theorem kStageOwn_know (h : ∀ s ∈ L, s.OK) : (kStageOwn L).Know := fun s hs => s.hOwn (h s hs)

theorem kStageOwn_point : (kStageOwn L).Point := fun s _ =>
  stageOwn_point s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW

theorem kStageOwn_local (h : ∀ s ∈ L, s.OK) (hR : ∀ s ∈ L, s.OKLocal) :
    (kStageOwn L).Local := fun s hs =>
  stageOwn_local s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW (h s hs).1.codes.1.1
    (h s hs).1.codes.1.2.1 (h s hs).1.codes.1.2.2 (hR s hs)

theorem kStageOwn_onOut : (kStageOwn L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kStageOwn_good (h : ∀ s ∈ L, s.OK) (hR : ∀ s ∈ L, s.OKLocal) :
    ∀ s ∈ L, ((kStageOwn L).block s).Good :=
  Kind.good (kStageOwn_know L h) (kStageOwn_point L) (kStageOwn_local L h hR) (kStageOwn_onOut L)

theorem kStageRide_know (h : ∀ s ∈ L, s.OK) : (kStageRide L).Know := fun s hs => s.hRide (h s hs)

theorem kStageRide_point : (kStageRide L).Point := fun s _ =>
  stageRide_point s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW

theorem kStageRide_local (h : ∀ s ∈ L, s.OK) (hR : ∀ s ∈ L, s.OKLocal) :
    (kStageRide L).Local := fun s hs =>
  stageRide_local s.Y s.sl s.e s.fx s.S s.Cw s.Pt s.lf s.lfW (h s hs).1.codes.1.1
    (h s hs).1.codes.1.2.1 (h s hs).1.codes.1.2.2 (hR s hs)

theorem kStageRide_onOut : (kStageRide L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kStageRide_good (h : ∀ s ∈ L, s.OK) (hR : ∀ s ∈ L, s.OKLocal) :
    ∀ s ∈ L, ((kStageRide L).block s).Good :=
  Kind.good (kStageRide_know L h) (kStageRide_point L) (kStageRide_local L h hR)
    (kStageRide_onOut L)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes that meet
the conditions. -/
def HStageOwn : Prop := ∀ L : List (StageSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kStageOwn L).Know

theorem hStageOwn : HStageOwn := kStageOwn_know

/-- The same for the stage whose fold's mask was sent earlier. -/
def HStageRide : Prop := ∀ L : List (StageSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kStageRide L).Know

theorem hStageRide : HStageRide := kStageRide_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hStageOwn
#print axioms VerifiableInference.OnPublicFiles.hStageRide
#print axioms VerifiableInference.OnPublicFiles.kStageOwn_good
#print axioms VerifiableInference.OnPublicFiles.kStageRide_good
