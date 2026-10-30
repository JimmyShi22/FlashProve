-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/Dec/EntryAtGate.lean: THE ENTRY FILE's NAMED HYPOTHESIS ON SOUNDNESS AT THE FRAME's NAMES, AT A GATED DECISION WHOSE GATE IS OPEN, FROM ONE PREMISE: "the library's written link,
at the new decision, is round-by-round sound at each instance's pair of records, at the library's own list of counts" (H of `soundAt_full_of_joh`, Johnson/Flat/Dec/SoundAtOfWritten.lean). The full size
and the small example. Joinings.
  `soundAt_bound`: `SoundAt` at a bound holds at every greater bound (`Err.Below.mono_bound`). (The head of SoundAtOfWritten.lean calls this step by a name that is another law's: owed words.)
  `entrySoundOfFullD_gated`: `entrySoundOfFullD` at dec := `gatedLinkDecision b (decOfXFull decE)`, b = true.
  `entrySoundOfFullD_of_joh`: THE CHAIN WHOLE: H ⟹ `CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T)` at ds := `dsFull`, xs := `frD.xs`, dec := that gate: 2^-128 ≤ T.εs rides in T (its field hε). Small alike.
Limits: H IS THE WHOLE LOAD (SoundAtOfWritten.lean's head). The bound 2^-128 counts work. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.SoundAtOfWritten
import Johnson.Flat.Dec.ClosedAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice TypedOracleCompiler.Run OnBytes.Tie
open _root_.Run.PQ (View CK XO)

/-- At a greater bound. -/
theorem soundAt_bound {T : Fmt.M1.Code} {v eM lg s : ℕ} {dec : XE AnsT lg s → View → Bool}
    {κ κ' : ℝ≥0∞} {C : CK} {ds : List TypedOracleCompiler.Run.PQ.RD} {a : ℕ} {xs : List XO} (h : κ ≤ κ')
    (hS : SoundAt T v eM lg s dec κ C ds a xs) : SoundAt T v eM lg s dec κ' C ds a xs := by
  obtain ⟨ε, hs, hb⟩ := hS
  exact ⟨ε, hs, _root_.Iop.Err.Below.mono_bound h hb⟩

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open TypedOracleCompiler.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List _root_.Run.PQ.XO} {decE : XE AnsT 29 1 → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

/-- At the gated decision, where the gate is open. -/
theorem entrySoundOfFullD_gated {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs (gatedLinkDecision b (decOfXFull decE)) rK rP depthReq
      early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs (gatedLinkDecision b (decOfXFull decE)) rK rP depthReq early
      salt K P)
    (hS : SoundAt frS.P.T frS.P.v frS.eM 29 1 decE T.εs (ckP .two) ds frS.P.T.a xs) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) := by
  subst hb
  exact entrySoundOfFullD (decE := decE) T hS

set_option maxRecDepth 100000 in
/-- **The chain whole: from the written link at the new decision.** -/
theorem entrySoundOfFullD_of_joh {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs (gatedLinkDecision b (decOfXFull decE)) rK rP
      depthReq early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs (gatedLinkDecision b (decOfXFull decE)) rK rP depthReq
      early salt K P)
    (H : ∀ x, (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
        (decE x)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recOf frS 29 1 (anT frS.P.v 1) x) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL))) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) :=
  entrySoundOfFullD_gated hb T (soundAt_bound T.hε (soundAt_full_of_joh decE H))

end Full

section Small
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD}
  {xs : List _root_.Run.PQ.XO} {decE : XE AnsT 19 1 → PQ.View → Bool} {rK rP : RecSmall}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

/-- At the gated decision, where the gate is open. -/
theorem entrySoundOfSmallD_gated {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs (gatedLinkDecision b (decOfXSmall decE)) rK rP depthReq
      early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP ds xs (gatedLinkDecision b (decOfXSmall decE)) rK rP depthReq early
      salt K P)
    (hS : SoundAt srS.P.T srS.P.v srS.eM 19 1 decE T.εs (ckP .two) ds srS.P.T.a xs) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) := by
  subst hb
  exact entrySoundOfSmallD (decE := decE) T hS

set_option maxRecDepth 100000 in
/-- **The chain whole: from the written link at the new decision.** -/
theorem entrySoundOfSmallD_of_joh {b : Bool} (hb : b = true)
    {P : (threeProtocolsAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsSmall srD.xs (gatedLinkDecision b (decOfXSmall decE)) rK rP
      depthReq early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtSmallSize A E DK DP runK runP dsSmall srD.xs (gatedLinkDecision b (decOfXSmall decE)) rK rP depthReq
      early salt K P)
    (H : ∀ x, (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
        (decE x)).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recOf srS 19 1 (anT srS.P.v 1) x) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL))) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtSmallSize T) :=
  entrySoundOfSmallD_gated hb T (soundAt_bound T.hε (soundAt_small_of_joh decE H))

end Small

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.soundAt_bound
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_gated
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_of_joh
#print axioms VerifiableInference.OnPublicFiles.entrySoundOfSmallD_of_joh
