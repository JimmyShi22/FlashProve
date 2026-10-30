-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/FamilyD.lean: a told record (`LayoutsByPublicReading`, Johnson/Top/InnerCompiledVerifierByPublicReading.lean, which
defines the terms) for every family of inputs of the full-size frame in which the entry file's
rounds, openings and decision are parameters (`InnerCompilerInputAndAnalysisFieldsAtFullSize`,
Johnson/Flat/Dec/TwoSizesAt.lean), whose members differ from one member T₀ in three fields alone:
cfg, m and enc. Definitions, statements and proofs.

Why: as in Johnson/Flat/Told/Family.lean.

Main names (namespace `VerifiableInference.OnPublicFiles`).
  `FamLettersD T₀`: the three public files; the three fields as functions of d (cfgOf, mOf, encT); a
    digest d₀ for the filler below.
  `lettersFamD U d`: T₀ with the three fields taken at d.
  `toldFamD U`: the record. d ranges over `D8`: the configuration's digest and a list of further
    digests. The public reading is `pub8 recordGround` (Johnson/Top/PreThreePub.lean). The public
    strings are the strings of a call with the number 169. The told part of d is its first component.
  `at_toldFamD`: the record's input at d is the frame's input at `lettersFamD U d`, by definition.
  `famD_noCoin`, `famD_asks`, `famD_once`: three of the six premises that the told theorem adds.
    They speak of the public reading alone.
  `core_toldFamD`: the fifteen hypotheses of `CompilerSoundnessConditions` at every d.

The premises of `core_toldFamD`: encT is one to one; nine tests on numbers (hk, bL, wLk, own, dL, wK,
dK, wP, dP); keySound, entrySound and proofSound (Johnson/Top/InnerCompiledVerifier.lean) at T₀'s own names. Two
more ride inside T₀: hSeed and hε.

What reads each part. d.1: cfgOf, mOf, encT and the told part. d.2: only cfgOf and mOf may read it.
T₀: every field of the input but the three. d₀: the filler alone.

Limits: as in Johnson/Flat/Told/Family.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.InnerCompiledVerifierByPublicReading
import Johnson.Top.PreThreePub
import Johnson.Flat.Dec.TwoSizesAt
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
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO} {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- The three public files, the three fields of the input that depend on the public reading's value d,
and a digest for the honest side's filler. -/
structure FamLettersD (T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) where
  pol : ByteArray
  KL : ByteArray
  lay : ByteArray
  /-- the field cfg, at d -/
  cfgOf : D8 → List (Dig 256)
  /-- the field m, at d: the coding of all typed queries as strings -/
  mOf : D8 → OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P) (List Bool) (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).annT (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).annL)) 256
  /-- the code of a key together with the told part of d -/
  encT : Dig 256 × KeyRoot 256 ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P) → Option ZKCP.Str
  /-- the digest in the honest side's filler -/
  d₀ : Dig 256

variable {T₀} (U : FamLettersD T₀)

/- Without this line Lean unfolds `pub8` where it compares two records, and runs out of recursion
depth. -/
attribute [local irreducible] pub8

/-- The family's member at d: T₀ with the three fields taken at d. -/
def lettersFamD (d : D8) : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P :=
  { T₀ with cfg := U.cfgOf d, m := U.mOf d, enc := fun k => U.encT (d.1, k) }

/-- The told record of the family. -/
def toldFamD : LayoutsByPublicReading (innerCompilerInputAtFullSize T₀) where
  D := D8
  Pub := pub8 recordGround U.pol U.KL U.lay
  Pt := OnBytes.Slice.IsCall169
  part := cfg8
  Sd := fun d => outOfDomainSampleQueryLayoutOfCode ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P) (List Bool) _ _ (v := frS.P.v) (lg := 29) (s := 1) T₀.t
    (U.cfgOf d) T₀.shape T₀.pl0 T₀.pl1 T₀.num (recSeedK recT recLg recS T₀.W.K T₀.hK) id seedEqFull
  cA := fun _ => codeA (v := frS.P.v) (s := 1)
  m := U.mOf
  encT := U.encT
  ISK := Unit
  commit := fun _ => .pure ((U.d₀, ⟨U.d₀, rK⟩), ())
  prove := fun _ b => .pure ⟨b.map fun _ => ⟨0, none, (U.d₀, rK, none), none⟩, List.length_map ..⟩
  π₀ := ((U.d₀, ⟨U.d₀, rK⟩), ⟨0, none, (U.d₀, rK, none), none⟩)

/-- The record's input at d is the frame's input at the family's member at d. -/
theorem at_toldFamD (d : D8) : (toldFamD U).at d = innerCompilerInputAtFullSize (lettersFamD U d) := rfl

theorem famD_noCoin : (toldFamD U).Pub.NoCoin := pub8_noCoin _ _ _ _

theorem famD_asks : (toldFamD U).Pub.AsksIn fun _ s => (toldFamD U).Pt s := pub8_asks169 _ _ _ _

theorem famD_once : NoRepeat (toldFamD U).Pub := pub8_noRepeat _ _ _ _

set_option maxRecDepth 20000 in
/-- The fifteen hypotheses of `CompilerSoundnessConditions` at every d, from the hypotheses on soundness at T₀'s own names,
the tests on numbers, and that encT is one to one. -/
theorem core_toldFamD (code : ZKCP.CodeIsOneToOne U.encT) (hk : kThree .two DK [] DP ≤ K)
    (bL : ∀ d ∈ ds, (bsRound .two d.entry d.kind).b ≤ K) (wLk : ∀ d ∈ ds, d.entry.work ≤ 64)
    (own : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true) (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize T₀))
    (eS : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T₀))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize T₀)) (d : (toldFamD U).D) :
    CompilerSoundnessConditions ((toldFamD U).beside (soundnessAnalysisDataAtFullSize T₀).Wn (soundnessAnalysisDataAtFullSize T₀).Rno (soundnessAnalysisDataAtFullSize T₀).x₀
                          (soundnessAnalysisDataAtFullSize T₀).εs d) :=
  (toldFamD U).core_from (soundnessAnalysisDataAtFullSize T₀) code ((threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).obj_noneColl P) kS
    eS pS (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).1 (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2.1
    (threeProtocolsAtFullSize_local A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2.2 (threeProtocolsAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).1 (threeProtocolsAtFullSize_entryCoherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt)
    (threeProtocolsAtFullSize_coherent A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).2 (wiresOfFullD A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt P K T₀.depthReqT hk bL wLk own dL wK dK wP dP)
    (fun _ => outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y =>
      le_trans (entryFull_seedLawK A (relationsAndEncodingOfClaims A E) T₀.W.K T₀.hK y) T₀.hε)
    (fun _ => codeA_inj) (fun _ => codeA_one) d

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.toldFamD
#print axioms VerifiableInference.OnPublicFiles.at_toldFamD
#print axioms VerifiableInference.OnPublicFiles.famD_noCoin
#print axioms VerifiableInference.OnPublicFiles.famD_asks
#print axioms VerifiableInference.OnPublicFiles.famD_once
#print axioms VerifiableInference.OnPublicFiles.core_toldFamD
