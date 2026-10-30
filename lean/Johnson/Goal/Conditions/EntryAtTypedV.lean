-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryAtTypedV.lean: the join (Johnson/Goal/Conditions/EntryAtDescV.lean:
entrySoundOfFullD_desc_codesV | SmallD) at the typed parameters frP | srP
(Johnson/Desc/K15/TypedP.lean): no premise on the link's parameters is left:
`CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T)` | `SmallD` at dec = `gatedLinkDecision b (decOfXFull (decDescFullV frP
plan ok))`, b = true: the seated description's run, at any plan and any public test, behind an open
gate. Each proof is one call:
samples = 1 · P.S · P.codes by rfl; PubAt · OpensAt by Johnson/Desc/K15/PubAtTyped.lean (the
kernel).
  entrySoundOfFullD_typedV | SmallD_typedV     at linkDescriptionAt frP | srP
  entrySoundOfFullD_linkV | SmallD_linkV       at (linkDescV c plan).run, outright, for any
  planner's record c, under the one decidable test sameP (p15Of c) frP | srP. At the full size that
  test is a law in scope
                                               (Johnson/Goal/Conditions/LinkTypedAtLines.lean:
                                               inScope_typed); the statement at the root itself
                                               is not in this library. At the small example it is
                                               evaluated true at one stored set; no theorem.
What rides: hSP : Desc.K15.SendPOfDecide (the tie's one named premise) · hb : b = true, tied
to nothing here · in T: hSeed and 2^-128 ≤ T.εs · the statement on codes
is filled by
Cb.Gl.bchks46At: the limit that travels with it: it rests on
the files under ThirdParty/, adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Not shown: that the decision in the slot is this dec (Where this and
lean/THEOREM.md differ, the page holds.) · all limits of EntryAtDescV.lean,
HsemAtV.lean, SoundAtOfWritten.lean, EntrySound.lean: an interactive protocol's round-by-round
soundness; the bound counts work; nothing on hashes,
bytes or the reader.
The statements are made by program, name for name, out of EntryAtTyped.lean (not in this library;
there of another decision), with hSP in front.

-/
import Johnson.Goal.Conditions.EntryAtDescV
import Johnson.Desc.K15.PubAtTyped
import Johnson.Desc.Link.LinkVariantLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open TypedOracleCompiler.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Params (recordRead smallRecordRead)
open _root_.Desc.K15 (SendPOfDecide frP srP fr_pubAt sr_pubAt fr_opensAt sr_opensAt decDescFullV
    decDescSmallV sameP p15Of linkDescV linkDescV_frP linkDescV_srP)

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

theorem entrySoundOfFullD_typedV (hSP : SendPOfDecide) (plan : List Fmt.DeclaredRound) (ok : Bool)
    {b : Bool} (hb : b = true)
    {dec : RecFull × RecFull → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXFull (decDescFullV frP plan ok)))
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) :=
  entrySoundOfFullD_desc_codesV hSP frP plan ok rfl rfl rfl fr_pubAt fr_opensAt hb er T

/-- **At (linkDescV c plan).run, outright**: c: the planner's record, ANY; plan: any. The decision
at an instance: the link's description's run at the two keys written of it. Where the test `sameP
(p15Of c) frP` says yes. -/
theorem entrySoundOfFullD_linkV (hSP : SendPOfDecide) (c : OnBytes.Model.Verify.Chains)
    (plan : List Fmt.DeclaredRound)
    (hP : sameP (p15Of c) frP = true) {b : Bool} (hb : b = true)
    {dec : RecFull × RecFull → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXFull fun x V =>
                  (linkDescV c plan).run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x) V))
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) :=
  entrySoundOfFullD_typedV hSP plan _ hb (er.trans (by rw [linkDescV_frP c plan hP]; rfl)) T

end Full

section Small
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecSmall}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

theorem entrySoundOfSmallD_typedV (hSP : SendPOfDecide) (plan : List Fmt.DeclaredRound) (ok : Bool)
    {b : Bool} (hb : b = true)
    {dec : RecSmall × RecSmall → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXSmall (decDescSmallV srP plan ok)))
    {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsSmall srD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP dsSmall srD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) :=
  entrySoundOfSmallD_desc_codesV hSP srP plan ok rfl rfl rfl sr_pubAt sr_opensAt hb er T

theorem entrySoundOfSmallD_linkV (hSP : SendPOfDecide) (c : OnBytes.Model.Verify.Chains)
    (plan : List Fmt.DeclaredRound)
    (hP : sameP (p15Of c) srP = true) {b : Bool} (hb : b = true)
    {dec : RecSmall × RecSmall → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXSmall fun x V =>
                  (linkDescV c plan).run (keysOfX srS.P.v 19 1 (anT srS.P.v 1) x) V))
    {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsSmall srD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP dsSmall srD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) :=
  entrySoundOfSmallD_typedV hSP plan _ hb (er.trans (by rw [linkDescV_srP c plan hP]; rfl)) T

end Small

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_typedV
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfSmallD_typedV
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_linkV
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfSmallD_linkV
