-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/PassAtBuilt.lean: THE PREMISES OF THE THIRD EXIT AT THE TOLD RECORD OF THE BUILT DESCRIPTION,
layoutsOfBuiltDescription (Johnson/FrontRoad/AtBuiltNamed.lean), for every DescriptionData, public files and reading: the coding's
first block is the hash function's (FirstIs), and the one test on first blocks fits the wires and the
seeds (PassFits). layoutsOfBuiltDescription is layoutsByPublicReadingAtDescriptionOfFields, which is S.layoutsByPublicReading, so these are firstIs_layoutsByPublicReading and passFits_layoutsByPublicReading
(Johnson/Goal/Conditions/HonestAtDescriptionDataAtFiles.lean). Nothing here is a goal.
-/
import Johnson.FrontRoad.AtBuiltNamed
import Johnson.Goal.Conditions.HonestAtDescriptionDataAtFiles

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open VerifierAndGoals FlashProve
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover VerifiableInference

variable (L : DescriptionData) (c₀ : Digest) (m₀ : List (_root_.Iop.Dig 256)) (Z : PublicFiles)

theorem firstIs_built (d : (layoutsOfBuiltDescription L c₀ m₀ Z).D) :
    FirstIs (k_pos (dataAtFiles L Z) c₀ m₀) ((layoutsOfBuiltDescription L c₀ m₀ Z).m d) :=
  firstIs_layoutsByPublicReading (dataAtFiles L Z) c₀ m₀ d

theorem passFits_built (d : (layoutsOfBuiltDescription L c₀ m₀ Z).D) :
    PassFits ((descriptionOfDataOnBytes L).input Z c₀ m₀).queryLayout ((layoutsOfBuiltDescription L c₀ m₀ Z).Sd d)
      (k_pos (dataAtFiles L Z) c₀ m₀) (firstBlockTestAtDescriptionData (dataAtFiles L Z) c₀ m₀) :=
  passFits_layoutsByPublicReading (dataAtFiles L Z) c₀ m₀ d

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.firstIs_built
#print axioms OnBytes.FrontRoad.passFits_built
