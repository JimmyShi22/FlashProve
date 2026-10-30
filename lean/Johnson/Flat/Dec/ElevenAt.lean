-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/ElevenAt.lean: eleven of the compiler's fifteen named hypotheses (`CompilerSoundnessConditionStatements`,
Johnson/Top/InnerCompiledVerifier.lean), one by one, at any record T of the frame's letters at the full size.

A TOOL, AND NO NEW CONTENT: each proof is the term that stands at that field in
`compilerSoundnessConditionsAtFullSize` (Johnson/Flat/Dec/TwoSizesAt.lean). That theorem gives the fifteen together and
therefore asks for the four that are left (keySound, entrySound, proofSound, commitment). Here the
eleven stand free of these four, with the frame's letters implicit, so that the instance at one
description's record is `‹x›_fullD T`: Lean then compares the letters in T's type and opens nothing.

Ten hold at every T. `wires_fullD` holds under the nine tests on numbers. `seedLaw_fullD` spends hK
and hε, which ride inside T.

Limits. Nothing on the four that are left, nor on the meaning. The full size alone.

-/
import Johnson.Flat.Dec.TwoSizesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).Provers}

set_option maxRecDepth 20000 in
/-- The decoder gives no index at a word that has a collision at the record's seed. -/
theorem noneColl_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.noneColl (r := innerCompilerInputAtFullSize T) :=
  (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).obj_noneColl P

set_option maxRecDepth 20000 in
/-- The key file's verifier reads its oracles at the declared positions alone. -/
theorem keyLocal_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.keyLocal (r := innerCompilerInputAtFullSize T) :=
  (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).1

set_option maxRecDepth 20000 in
/-- The entry file's. -/
theorem entryLocal_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entryLocal (r := innerCompilerInputAtFullSize T) :=
  (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).2.1

set_option maxRecDepth 20000 in
/-- The proof file's. -/
theorem proofLocal_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.proofLocal (r := innerCompilerInputAtFullSize T) :=
  (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).2.2

set_option maxRecDepth 20000 in
/-- The key file's marks fit together round by round. -/
theorem keyCoherent_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.keyCoherent (r := innerCompilerInputAtFullSize T) :=
  (threeProtocolsAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).1

set_option maxRecDepth 20000 in
/-- The entry file's. -/
theorem entryCoherent_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entryCoherent (r := innerCompilerInputAtFullSize T) :=
  threeProtocolsAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt

set_option maxRecDepth 20000 in
/-- The proof file's. -/
theorem proofCoherent_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.proofCoherent (r := innerCompilerInputAtFullSize T) :=
  (threeProtocolsAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early
    salt).2

set_option maxRecDepth 20000 in
/-- The seed made from uniform digests: it spends hK and hε, which ride inside T. -/
theorem seedLaw_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.seedLaw (soundnessAnalysisDataAtFullSize T) :=
  outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
    le_trans (entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T.W.K T.hK y) T.hε

set_option maxRecDepth 20000 in
/-- No two lists of answers are written as the same list of digests. -/
theorem answersCode_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.answersCode (r := innerCompilerInputAtFullSize T) :=
  codeA_inj

set_option maxRecDepth 20000 in
/-- All lists of answers are written with one number of digests. -/
theorem answersLength_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.answersLength (r := innerCompilerInputAtFullSize T) :=
  codeA_one

set_option maxRecDepth 20000 in
/-- The four wires' laws, under the nine tests on numbers. -/
theorem wires_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hk : kThree .two DK [] DP ≤ K) (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K)
    (wLk : ∀ d ∈ ds, d.entry.work ≤ 64) (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) (wK : DK.workFit = true)
    (dK : DK.depthFit = true) (wP : DP.workFit = true) (dP : DP.depthFit = true) :
    CompilerSoundnessConditionStatements.wires (r := innerCompilerInputAtFullSize T) :=
  wiresOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K
    T.depthReqT hk bL wLk own dL wK dK wP dP

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.noneColl_fullD
#print axioms VerifiableInference.OnPublicFiles.keyLocal_fullD
#print axioms VerifiableInference.OnPublicFiles.entryLocal_fullD
#print axioms VerifiableInference.OnPublicFiles.proofLocal_fullD
#print axioms VerifiableInference.OnPublicFiles.keyCoherent_fullD
#print axioms VerifiableInference.OnPublicFiles.entryCoherent_fullD
#print axioms VerifiableInference.OnPublicFiles.proofCoherent_fullD
#print axioms VerifiableInference.OnPublicFiles.seedLaw_fullD
#print axioms VerifiableInference.OnPublicFiles.answersCode_fullD
#print axioms VerifiableInference.OnPublicFiles.answersLength_fullD
#print axioms VerifiableInference.OnPublicFiles.wires_fullD
