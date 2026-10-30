-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryWrittenLaw.lean: THE WRITTEN VALUE FOR THE SLOT IS, BY THE KERNEL, THE CONSTANT OF WHICH THE LINK's LAW SPEAKS, AT ONE PLAN AND ONE BOOL.
  decWritten_is     AT EVERY PARAMETER FILE: linkDecisionAtParameterFile pol says no to all, or linkDecisionAtParameterFile pol = fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr): decDescFullV: the constant of which the link's law speaks (HsemAtV.lean)
  decWritten_at     at a parameter file whose first lines read as recordLines it IS the second (with the closed made_full): «NOT no to all» IS SAID OF THE OUTER MATCH ALONE: no theorem here has a yes of the run
  decWritten_inScope   the same at every three public files in the goals' scope
  linkAt_full | linkAt_small   the written link WHOLE: ⟨the description at the typed parameters, dsFull | dsSmall, frD.xs | srD.xs⟩: the frame's own letters
OBJECT: Desc.K15.linkDecisionAtParameterFile (the entry file's decision in the description: `FlashProve.linkDecisionAtFiles`, Johnson/Goal/Description/LinkDec.lean) · Desc.K15.decDescFullV · USER: entrySoundOfFullD_written (decWritten_is) · LETTERS: none. THE LAW AT THE SEAT ITSELF IS Johnson/Goal/Conditions/EntryAtWritten.lean's entrySoundOfFullD_written.
Equations alone: nothing on soundness.
-/
import Johnson.Goal.Conditions.EntryWrittenEq
import Johnson.Desc.Link.LinkWrittenMade
import Johnson.Desc.K15.TypedV

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Flat TypedOracleCompiler.Slice OnBytes.Tie

theorem decWritten_is (pol : ByteArray) : linkDecisionAtParameterFile pol = (fun _ _ => false) ∨
    linkDecisionAtParameterFile pol = fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) :=
  decWritten_cases pol

theorem decWritten_at {pol b : ByteArray} (h : Params.readLines pol = .ok (recordLines, b)) :
    linkDecisionAtParameterFile pol = fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) := by
  obtain ⟨L, hL⟩ := made_full
  unfold linkDecisionAtParameterFile
  rw [h]
  simp only [if_true, hL]
  rw [linkAt_F hL]
  rfl

/-- **In scope the value is live**: at every three public files in the goals' scope the written value IS the description's run (scope_reads with decWritten_at). «Live» is said of the OUTER match alone: that the run accepts
anything is shown by no theorem here. -/
theorem decWritten_inScope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) :
    linkDecisionAtParameterFile Z.pol = fun rr => decDescFullV frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan) (recX rr) := by
  obtain ⟨b, hb⟩ := scope_reads hZ
  exact decWritten_at hb

/-- **The written link, whole, at the full size**: the description at the typed parameters WITH THE FRAME's OWN LETTERS: the compiler's rounds dsFull and the stored openings frD.xs. -/
theorem linkAt_full : linkAt frP recordPlan = .ok ⟨linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan), OnBytes.Flat.dsFull, OnBytes.Slice.frD.xs⟩ := by
  have hw : (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).planWord = none := by
    unfold OneChainFileDescription.planWord
    rw [if_pos planOk_full]
  unfold linkAt
  simp only [hw, fr_ds, fr_xs]

/-- The like at the small size. -/
theorem linkAt_small : linkAt srP smallRecordPlan = .ok ⟨linkDescriptionAt srP (linkDeclaredRounds srP) (linkRoundsMatchPlan srP smallRecordPlan), OnBytes.Flat.dsSmall, OnBytes.Slice.srD.xs⟩ := by
  have hw : (linkDescriptionAt srP (linkDeclaredRounds srP) (linkRoundsMatchPlan srP smallRecordPlan)).planWord = none := by
    unfold OneChainFileDescription.planWord
    rw [if_pos planOk_small]
  unfold linkAt
  simp only [hw, sr_ds, sr_xs]

end Desc.K15

#print axioms Desc.K15.linkAt_full
#print axioms Desc.K15.linkAt_small
#print axioms Desc.K15.decWritten_is
#print axioms Desc.K15.decWritten_at
#print axioms Desc.K15.decWritten_inScope
