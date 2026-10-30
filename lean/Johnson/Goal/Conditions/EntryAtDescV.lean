-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryAtDescV.lean: the join of the entry file's "hsem" at the seated link
(Johnson/Desc/K15/HsemAtV.lean: `H_fullV` | `H_smallV`) to the conditional theorem's named
hypothesis on the entry file's soundness, at the names of
the frame with the entry file's three letters: `CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T)` | `SmallD`,
at the decision dec = `gatedLinkDecision b (decOfXFull (decDescFullV P plan ok))`, b = true: the seated
description's run at the two keys written of the
two records, behind a gate. No run of `verify-on-bytes` stands in that decision.
Each proof: "subst", then two calls: `entrySoundOfFullD_of_joh` (Johnson/Flat/Dec/EntryAtGate.lean)
at `H_fullV`.
  `entrySoundOfFullD_descV` | `entrySoundOfSmallD_descV`: under `Cb.BCHKS46At` as a hypothesis.
  `entrySoundOfFullD_desc_codesV` | `Small`: that hypothesis filled by `Cb.Gl.bchks46At`
  (Cb/Bridge/GlCodesProved.lean). The limit that then travels with the theorem: it rests on
  the files under ThirdParty/, adapted from ArkLib
    and Mathlib (lean/LIMITS.md, L15).

Premises left: hSP : Desc.K15.SendPOfDecide (Johnson/Desc/K15/SendOwnLaw.lean): the one named
premise of the tie between the seated link and the laws' middle term: a proposition on the kind K1's
own block, proved by `sendPOfDecide` (Johnson/Desc/K15/SendOwnPaid.lean; no premise) ·
H_fullV's | H_smallV's five on P: P.set.samples = 1 · P.S | P.codes = the typed record's · PubAt P
frC | srC · OpensAt P frC | srC: all five are proved at frP | srP, the last two by the kernel
(Johnson/Desc/K15/PubAtTyped.lean): see
EntryAtTypedV.lean · hb : b = true: tied to nothing here: what the slot's gate is, is the frame's to
say · in T ride hSeed and 2^-128 ≤ T.εs.
Limits: those of HsemAtV.lean, SoundAtOfWritten.lean, EntrySound.lean. The bound 2^-128 counts work.
An interactive protocol's round-by-round soundness; nothing on hashes, bytes or the reader. Nothing
on hiding.

-/
import Johnson.Desc.K15.HsemAtV
import Johnson.Flat.Dec.EntryAtGate
import Cb.Bridge.GlCodesProved

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
open _root_.Desc.K15 (SendPOfDecide P15 PubAt OpensAt decDescFullV decDescSmallV H_fullV H_smallV)

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

set_option maxRecDepth 100000 in
/-- **The entry file's hypothesis on soundness at the link's own description's run, behind an open
gate.** -/
theorem entrySoundOfFullD_descV (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (Pk : P15)
    (plan : List Fmt.DeclaredRound) (ok : Bool)
    (hs : Pk.set.samples = 1) (hS : Pk.S = recordRead.link) (hC : Pk.codes = recordRead.codes)
    (hpub : PubAt Pk frC recordRead.codes) (hopen : OpensAt Pk frC) {b : Bool} (hb : b = true)
    {dec : RecFull × RecFull → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXFull (decDescFullV Pk plan ok)))
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) := by
  subst er
  exact entrySoundOfFullD_of_joh hb T (H_fullV hSP hA Pk plan ok hs hS hC hpub hopen)

/-- The same with the statement on codes filled by `Cb.Gl.bchks46At` (see the head for the limit
that travels with it). -/
theorem entrySoundOfFullD_desc_codesV (hSP : SendPOfDecide) (Pk : P15) (plan : List Fmt.DeclaredRound)
    (ok : Bool)
    (hs : Pk.set.samples = 1) (hS : Pk.S = recordRead.link) (hC : Pk.codes = recordRead.codes)
    (hpub : PubAt Pk frC recordRead.codes) (hopen : OpensAt Pk frC) {b : Bool} (hb : b = true)
    {dec : RecFull × RecFull → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXFull (decDescFullV Pk plan ok)))
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) :=
  entrySoundOfFullD_descV hSP Cb.Gl.bchks46At Pk plan ok hs hS hC hpub hopen hb er T

end Full

section Small
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecSmall}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

set_option maxRecDepth 100000 in
/-- **The entry file's hypothesis on soundness at the link's own description's run, behind an open
gate.** -/
theorem entrySoundOfSmallD_descV (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (Pk : P15)
    (plan : List Fmt.DeclaredRound) (ok : Bool)
    (hs : Pk.set.samples = 1) (hS : Pk.S = smallRecordRead.link)
        (hC : Pk.codes = smallRecordRead.codes)
    (hpub : PubAt Pk srC smallRecordRead.codes) (hopen : OpensAt Pk srC) {b : Bool} (hb : b = true)
    {dec : RecSmall × RecSmall → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXSmall (decDescSmallV Pk plan ok)))
    {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsSmall srD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP dsSmall srD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) := by
  subst er
  exact entrySoundOfSmallD_of_joh hb T (H_smallV hSP hA Pk plan ok hs hS hC hpub hopen)

/-- The same with the statement on codes filled by `Cb.Gl.bchks46At` (see the head for the limit
that travels with it). -/
theorem entrySoundOfSmallD_desc_codesV (hSP : SendPOfDecide) (Pk : P15) (plan : List Fmt.DeclaredRound)
    (ok : Bool)
    (hs : Pk.set.samples = 1) (hS : Pk.S = smallRecordRead.link)
        (hC : Pk.codes = smallRecordRead.codes)
    (hpub : PubAt Pk srC smallRecordRead.codes) (hopen : OpensAt Pk srC) {b : Bool} (hb : b = true)
    {dec : RecSmall × RecSmall → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (decOfXSmall (decDescSmallV Pk plan ok)))
    {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsSmall srD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP dsSmall srD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) :=
  entrySoundOfSmallD_descV hSP Cb.Gl.bchks46At Pk plan ok hs hS hC hpub hopen hb er T

end Small

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_descV
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfSmallD_descV
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_desc_codesV
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfSmallD_desc_codesV
