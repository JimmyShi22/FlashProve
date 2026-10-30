-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FileDecidesProof.lean: the proof of `FileDecides`
(Johnson/Desc/Sound/FileRule.lean): it is the library's `rowOf_of_whole`
(OnBytes/Maker/RowWhole.lean) with `Row.all_out` (OnBytes/TypedOracleCompiler/Joined/OfLinks.lean).

Limits: those of the sheet.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker

theorem fileDecides : FileDecides := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T okF okJ ok3 silent P hfit hF hJ h3 x y τ h
  have k := rowOf_of_whole C D tF tJ t3 all all okF okJ ok3 T.run₁ T.run₂ T.run₃ silent hfit hF hJ
    h3 x y τ h
  rw [_root_.CompileK.Joined.Row.all_out]
  have k' : (T.row tF tJ t3 okF okJ ok3).ior.out x y τ = some () := k
  rw [k']
  rfl

end VerifiableInference.Desc.Sound
