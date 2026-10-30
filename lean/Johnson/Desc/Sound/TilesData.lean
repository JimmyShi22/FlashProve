-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TilesData.lean: the stretches tile the chains AT EVERY DESCRIPTION OF A FILE. A
SHEET OF STATEMENTS: definitions, and propositions written as `def … : Prop`. NOTHING IS PROVED IN
THIS FILE.

Johnson/Desc/Sound/Tiles.lean has the maker of the pieces (`cutRow`), the list of all trees
(`allOf`) and the statements at three lists of written rounds. Here the same is said of a `FileDescription`
F (Johnson/Desc/Block.lean) and the data D that `FileDescription.data` (Johnson/Desc/BlockSlot.lean) makes
of F's own declared rounds: FOR EVERY F, WHATEVER BLOCKS STAND IN IT, every name of a file and every
D with `F.data file = .ok D`.
  `FileDescription.sealLast`: a test on the plan: the first chain's last block has a round.
  `FlatSome`: each of the three chains has a block.
  `RowFitOfData`: `RowFit D (allOf D) (allOf D)`.
  `FitsOfData`: `Three.Fits` at every `Three` over D and `allOf D` whose pieces are the maker's, at
    blocks that declare, block by block, the rounds that F's blocks declare (so at F's blocks
    themselves, and at these lifted to a wider record or with a test laid in front: `Block.lift`,
    `below`).
Limits: those of Tiles.lean. `F.sealLast = true` and `F.data file = .ok D` are premises: two tests
on the plan, which can be evaluated. `F.planOk` is no premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Tiles
import Johnson.Desc.BlockSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

-- FileDescription.sealLast: Johnson/Desc/Block.lean's own.

end VerifiableInference.Desc

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)

/-- Each of the three chains has a block. -/
def FlatSome : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.first.blocksInOrder ≠ [] ∧ F.shared.blocksInOrder ≠ [] ∧ F.second.blocksInOrder ≠ []

/-- What the comparison of the three stages with the whole file asks, at the list of all trees. -/
def RowFitOfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    RowFit D (allOf D) (allOf D)

/-- **The stretches tile the three chains of every description.** -/
def FitsOfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    F.sealLast = true →
    ∀ (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type) (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W)
      (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl)) (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
      (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl)) rest₁ rest₂ rest₃ (r : Fmt.RoundView),
      (b₁ :: l₁).map (·.rounds) = F.first.blocksInOrder.map (·.rounds) →
      (b₂ :: l₂).map (·.rounds) = F.shared.blocksInOrder.map (·.rounds) →
      (b₃ :: l₃).map (·.rounds) = F.second.blocksInOrder.map (·.rounds) →
      T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r → T.Fits


end VerifiableInference.Desc.Sound
