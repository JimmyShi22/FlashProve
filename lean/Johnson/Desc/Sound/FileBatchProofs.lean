-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FileBatchProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/FileBatch.lean, and of three of the five of SharedSeam.lean: `RunOfStarts₁`,
`RunOfStarts`, `RunOfStarts₃`. The other two, `SeamLink` and `SeamOfGood`, are proved in
Johnson/Desc/Sound/SharedSeamProofs.lean.

Limits: those of Johnson/Desc/Sound/FileBatch.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FileBatch
import Johnson.Desc.Sound.SharedSeamProofs
import Johnson.Desc.Sound.FileKnowsJ
import Johnson.Desc.Sound.FoldBelowProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

theorem runOfStarts₁ : RunOfStarts₁ := runOfStarts₁_of foldBelow
theorem runOfStarts : RunOfStarts := runOfStarts_of foldBelow
theorem runOfStarts₃ : RunOfStarts₃ := runOfStarts₃_of foldBelow

theorem fileKnowsJOfKeyed : FileKnowsJOfKeyed := by
  intro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N kA kZ k₁ k₂
    F₁ hF g₁ hk g₃ hG hk₁ law₁ law₂
  exact fileKnowsJ C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N
    k₁ k₂ F₁ hF g₁ g₃ hG.glue₁ hG.ends hk₁
    (seamLink C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N kA
      kZ k₁ k₂ hF hk hG.glue₂ law₁ law₂)

theorem fileKnowsJOfGood : FileKnowsJOfGood := by
  intro C D all Y S₁ S₂ S₀ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N get set Ra Rc
    F₁ hF g₁ g₃ hG hQ hg hr hk e1 e2 hb ho hk₁
  exact fileKnowsJ C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 _ _ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N
    _ _ F₁ hF g₁ g₃ hG.glue₁ hG.ends hk₁
    (seamOfGood C D all Y S₁ S₂ S₀ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N get
      set Ra Rc hF hQ hg hr hk e1 e2 hb ho hG.glue₂)

end VerifiableInference.Desc.Sound
