-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsOkProofs.lean: where the blocks' declared rounds are the plan's, THE DATA
MADE OF THE DESCRIPTION ARE THE PLAN's DATA. Statements (`def … : Prop`) and their proofs.
  `decl_of_planOk`: a yes of `F.planOk` gives `F.roundsDeclaredByBlocks = F.plans`: the blocks' declared rounds in a
    row are the rounds that the description holds as the plan's, whole.
  `DataIsPlans`: m: what the planner and `sendsOf` make of the three public files. If `declPOf m`
    returns P, `depthOf m` returns the description's `tableDepth`, THE BLOCKS' DECLARED ROUNDS IN A
    ROW ARE P, WHOLE (`F.roundsDeclaredByBlocks = P`: at P := `F.plans` it is what `decl_of_planOk` gives), and
    `F.data "proof file"` returns D, then `dataPAt m`
    returns that same D. So the stretches that tile D (Johnson/Desc/Sound/TilesData.lean) tile the
    plan's own data, and an error that is counted at the plan's data is counted at the data of the
    compiled description.
  `DataIsPlansK`: the like for a key file (`declKOf`, `dataKAt`, "key file").
Limits. That `declPOf`'s rule is the protocol's is not said. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.TilesDataProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Johnson.G.OfPlan
open OnBytes.Params (Rounds)

/-- A yes of the tests on the plan gives: the blocks' declared rounds in a row are the plan's,
whole. -/
theorem decl_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) : F.roundsDeclaredByBlocks = F.plans := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact Prod.ext h1 (Prod.ext h2 h3)

/-- **The data made of the description are the plan's data**: a proof file. -/
def DataIsPlans : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (m : Made) (P : Decl3) (D : WholeD),
    declPOf m = .ok P → depthOf m = .ok F.tableDepth → F.roundsDeclaredByBlocks = P →
    F.data "proof file" = .ok D → dataPAt m = .ok D

/-- The like for a key file. -/
def DataIsPlansK : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (m : Made) (P : Decl3) (D : WholeD),
    declKOf m = .ok P → depthOf m = .ok F.tableDepth → F.roundsDeclaredByBlocks = P →
    F.data "key file" = .ok D → dataKAt m = .ok D

theorem dataIsPlans : DataIsPlans := by
  intro Xi F m P D hP ha e hD
  obtain ⟨R, hR, hok, rfl⟩ := data_ok F "proof file" D hD
  unfold dataPAt
  rw [ha, hP, ← e]
  show (do
    let R' ← writtenOf "proof file" F.roundsDeclaredByBlocks
    pure (WholeD.of F.tableDepth (dataAt F.tableDepth (some R'))) : Except String WholeD) = _
  rw [hR]
  show Except.ok (WholeD.of F.tableDepth (dataAt F.tableDepth (some R))) = _
  unfold dataAt
  rw [if_pos hok]

theorem dataIsPlansK : DataIsPlansK := by
  intro Xi F m P D hP ha e hD
  obtain ⟨R, hR, hok, rfl⟩ := data_ok F "key file" D hD
  unfold dataKAt
  rw [ha, hP, ← e]
  show (do
    let R' ← writtenOf "key file" F.roundsDeclaredByBlocks
    pure (WholeD.of F.tableDepth (dataAt F.tableDepth (some R'))) : Except String WholeD) = _
  rw [hR]
  show Except.ok (WholeD.of F.tableDepth (dataAt F.tableDepth (some R))) = _
  unfold dataAt
  rw [if_pos hok]

end VerifiableInference.Desc.Sound
