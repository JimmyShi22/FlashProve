-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Told/Family.lean: a told record (`LayoutsByPublicReading`, Johnson/Top/InnerCompiledVerifierByPublicReading.lean, which
defines the terms) for every family of inputs of the full-size frame (`InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize`,
Johnson/Flat/TwoSizesAt.lean) whose members differ from one member T₀ in three fields alone: cfg, m
and enc. Definitions, statements and proofs.

Why. `innerCompiledVerifier_sound_byPublicReading` speaks of a verifier that first reads public values d off the hash
function and then runs the compiled verifier at an input that depends on d. It asks for a record of
how the input depends on d. In a description of a real run, the input depends on d through these
three fields. This file builds the record once, for every such family.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `FamLetters T₀`: the three public files; the three fields as functions of d (cfgOf, mOf, encT); a
    digest d₀ for the filler below.
  `lettersFam U d`: T₀ with the three fields taken at d.
  `toldFam U`: the record. d ranges over `D8`: the configuration's digest and a list of further
    digests. The public reading is `pub8 recordGround` (Johnson/Top/PreThreePub.lean). The public
    strings are the strings of a call with the number 169. The told part of d is its first component.
  `at_toldFam`: the record's input at d is the frame's input at `lettersFam U d`, by definition.
  `fam_noCoin`, `fam_asks`, `fam_once`: three of the six premises that the told theorem adds.
    They speak of the public reading alone.
  `core_toldFam`: the fifteen hypotheses of `CompilerSoundnessConditions` at every d.

The premises of `core_toldFam`: encT is one to one; the statement on codes (hA); five tests on numbers
(hk, wK, dK, wP, dP); keySound and proofSound (Johnson/Top/InnerCompiledVerifier.lean) at T₀'s own names. Two
more ride inside T₀: hSeed and hε.

What reads each part. d.1: cfgOf, mOf, encT and the told part. d.2: only cfgOf and mOf may read it.
T₀: every field of the input but the three. d₀: the filler alone.

Limits.
- The other three added premises (spare, word, code) speak of mOf and encT; none is proved here, and
  code is a premise of `core_toldFam`.
- The record's honest side (commit, prove, π₀) is a filler: a fixed key and proofs without a proof
  string. No statement on soundness reads it.
- Every statement holds whatever the decisions runK and runP are, also at one that accepts
  everything. The record judges no verifier: the hypotheses on soundness do, and they stay premises.
- The public files are fixed before the hash function is drawn.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.InnerCompiledVerifierByPublicReading
import Johnson.Top.PreThreePub
import Johnson.Flat.TwoSizesAt
import Johnson.PV.ToldThin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)

/-- The three public files, the three fields of the input that depend on the public reading's value d,
and a digest for the honest side's filler. -/
structure FamLetters (T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P) where
  pol : ByteArray
  KL : ByteArray
  lay : ByteArray
  /-- the field cfg, at d -/
  cfgOf : D8 → List (Dig 256)
  /-- the field m, at d: the coding of all typed queries as strings -/
  mOf : D8 → OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).withProvers P) (List Bool) (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).annT (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).annL)) 256
  /-- the code of a key together with the told part of d -/
  encT : Dig 256 × KeyRoot 256 ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).withProvers P) → Option ZKCP.Str
  /-- the digest in the honest side's filler -/
  d₀ : Dig 256

variable {T₀} (U : FamLetters T₀)

/-- The family's member at d: T₀ with the three fields taken at d. -/
def lettersFam (d : D8) : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P :=
  { T₀ with cfg := U.cfgOf d, m := U.mOf d, enc := fun k => U.encT (d.1, k) }

/-- The told record of the family. -/
def toldFam : LayoutsByPublicReading (innerCompilerInputWithFixedLinkAtFullSize T₀) where
  D := D8
  Pub := pub8 recordGround U.pol U.KL U.lay
  Pt := OnBytes.Slice.IsCall169
  part := cfg8
  Sd := fun d => outOfDomainSampleQueryLayoutOfCode ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).withProvers P) (List Bool) _ _ (v := frS.P.v) (lg := 29) (s := 1) T₀.t
    (U.cfgOf d) T₀.shape T₀.pl0 T₀.pl1 T₀.num (recSeedK recT recLg recS T₀.W.K T₀.hK) id seedEqFull
  cA := fun _ => codeA (v := frS.P.v) (s := 1)
  m := U.mOf
  encT := U.encT
  ISK := Unit
  commit := fun _ => .pure ((U.d₀, ⟨U.d₀, rK⟩), ())
  prove := fun _ b => .pure ⟨b.map fun _ => ⟨0, none, (U.d₀, rK, none), none⟩, List.length_map ..⟩
  π₀ := ((U.d₀, ⟨U.d₀, rK⟩), ⟨0, none, (U.d₀, rK, none), none⟩)

/-- The record's input at d is the frame's input at the family's member at d. -/
theorem at_toldFam (d : D8) : (toldFam U).at d = innerCompilerInputWithFixedLinkAtFullSize (lettersFam U d) := rfl

set_option maxRecDepth 20000 in
theorem fam_noCoin : (toldFam U).Pub.NoCoin := pub8_noCoin _ _ _ _

theorem fam_asks : (toldFam U).Pub.AsksIn fun _ s => (toldFam U).Pt s := pub8_asks169 _ _ _ _

theorem fam_once : NoRepeat (toldFam U).Pub := pub8_noRepeat _ _ _ _

set_option maxRecDepth 20000 in
/-- The fifteen hypotheses of `CompilerSoundnessConditions` at every d, from the statement on codes, the hypotheses on
soundness at T₀'s own names, the tests on numbers, and that encT is one to one. -/
theorem core_toldFam (code : ZKCP.CodeIsOneToOne U.encT) (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T₀)) (d : (toldFam U).D) :
    CompilerSoundnessConditions ((toldFam U).beside (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Wn (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).Rno (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).x₀
                          (soundnessAnalysisDataWithFixedLinkAtFullSize T₀).εs d) :=
  (toldFam U).core_from (soundnessAnalysisDataWithFixedLinkAtFullSize T₀) code ((threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).obj_noneColl P) kS
    (entrySoundWithFixedLinkAtFullSize hA T₀) pS (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1 (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.1
    (threeProtocolsWithFixedLinkAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2.2 (threeProtocolsWithFixedLinkAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).1 (threeProtocolsWithFixedLinkAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt)
    (threeProtocolsWithFixedLinkAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).2 (wiresOfFull A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt P K T₀.depthReqT hk wK dK wP dP)
    (fun _ => outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
      le_trans (entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T₀.W.K T₀.hK y) T₀.hε)
    (fun _ => codeA_inj) (fun _ => codeA_one) d

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.toldFam
#print axioms VerifiableInference.OnPublicFiles.at_toldFam
#print axioms VerifiableInference.OnPublicFiles.fam_noCoin
#print axioms VerifiableInference.OnPublicFiles.fam_asks
#print axioms VerifiableInference.OnPublicFiles.fam_once
#print axioms VerifiableInference.OnPublicFiles.core_toldFam
