-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/WholeRunAtSizes.lean: at the two sizes of the default setting, with the written rounds'
data and the two decisions as letters (Johnson/Flat/TwoSizesAt.lean): the key file's named
hypothesis on soundness from the law `RunMeets` (Johnson/Flat/WholeRun.lean) and eight premises
more, and the compiler's theorem with that hypothesis exchanged for the law and eight premises more.

Statements and proofs; each is one call, or two, one inside the other (Small for Full at the small
size).
  `keySoundOfFull_of_runMeets`: `CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T)`: `keySound_of_runMeets` at
    `threeProtocolsWithFixedLinkAtFullSize`'s letters.
  `innerCompiledVerifierSoundWithFixedLinkAtFullSize_of_runMeets`: `innerCompiledVerifierSoundWithFixedLinkAtFullSize_for` at ⟨that, proofSound, commitment⟩: of the three
    hypotheses that `RemainingSoundnessConditionsWithFixedLinkAtFullSize` leaves, two are left by name; in the third's place stand the law
    and eight premises more, a typed protocol's soundness among them: an exchange, not a payment.

Does not show: the law, the maps, or the typed protocol's soundness at any data or decision.
`proofSound`, `commitment`, the meaning. What the heads of the two files named do not show. This
file's own limits: the input `innerCompilerInputWithFixedLinkAtFullSize T` is fixed before the hash function is drawn; no
inhabitant of `InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize` | `Small` stands; T.εs (at least 2^-128) and the rounds' work in
DK are letters: where T.εs is not below every round's 2^-work the key file's hypothesis can be had
from the proof of work alone; `wK` bounds every round's work by 64, so below 2^-64 that case is shut
at all data that the second theorem admits, and from there up it hangs on the data (an argument; no
theorem). The factor 2 ^ T.depthReqT in `below₂` is a field that whoever fills T picks: nothing here
ties it to DK. bl', er', rd' are carried through all four statements and read by nothing. Two things
ride along from Johnson/Flat/TwoSizesAt.lean, as its head says: the entry file's part in T's type
and in `innerSystem`, whose decision is a run of the program's routine; and the makers' dry runs
beneath its import of Johnson/Flat/TwoSizes.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TwoSizesAt
import Johnson.Flat.WholeRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX)

/-! ## The full size -/

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P)
  {s₁' s₂' s₃' : Shape} (M₁ : Maps (DK.at frS.P.T.a).ds₁ s₁')
  (M₂ : Maps (DK.at frS.P.T.a).ds₂ s₂') (M₃ : Maps (DK.at frS.P.T.a).ds₃ s₃') {X' : Type}
  {E' : ExtSpec} (fx : RecFull → X') (fy : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str → E'.Str)
  (acc' : X' → E'.Str → Tr (s₁' ++ (s₂' ++ s₃')) → Bool)

/-- **The key file's named hypothesis on soundness at this size**, from nine premises: the law at
the key file's data and decision (`meets`); `Maps.OK` of the three lists of maps (`ok₁`, `ok₂`,
`ok₃`); a typed protocol's soundness (`sound`), which is shown nowhere here; the translation of the
languages (`lang`); three bounds on counts at T.εs (`held₁`, `below₂`, `held₃`). The law alone gives
nothing (`runMeets_top`). One call of `keySound_of_runMeets`. -/
theorem keySoundOfFull_of_runMeets
    (meets : RunMeets (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty M₁ M₂ M₃ silK runK fx
      fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃')
    (L' : X' → E'.Str → Prop)
    (lang : ∀ rec y, L' (fx rec) (fy y) →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).coll y rec.1 ∨ (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).D y rec ≠ none)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃)))
    (held₁ : M₁.Held T.εs δ₁)
    (below₂ : Err.Below (Err.times (2 ^ T.depthReqT) (M₂.err δ₂)) T.εs)
    (held₃ : M₃.Held T.εs δ₃) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtFullSize T) :=
  keySound_of_runMeets (lettersAt A (relationsAndEncodingOfClaims A E)) DK DP (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty silK runK silP runP (entryFullQ salt) (2 ^ depthReq)
    early none P T.letters T.names M₁ M₂ M₃ fx fy acc' meets bl' er' rd' ok₁ ok₂ ok₃ δ₁ δ₂ δ₃ L'
    lang sound held₁ below₂ held₃

/-- **The compiler's theorem at this size, for any claim, with the key file's hypothesis exchanged
for the nine premises of `keySoundOfFull_of_runMeets`.** Left, all hypotheses of the theorem: these
nine (`meets`; `ok₁`, `ok₂`, `ok₃`; `lang`; `sound`, a typed protocol's soundness; `held₁`,
`below₂`, `held₃`); `proofSound`; `commitment`; the meaning (`hs`); the theorem on codes (`hA`) and
the five tests on numbers (`hk`, `wK`, `dK`, `wP`, `dP`) of `innerCompiledVerifierSoundWithFixedLinkAtFullSize_for`; and, inside T,
hSeed and hε. Lean's list of axioms does not show them. Not in this list: the laws that stand in the
letters' types (T.m : `OracleCoding`, a coding one to one and onto; A.mat_cut): TwoSizesAt.lean's head. -/
theorem innerCompiledVerifierSoundWithFixedLinkAtFullSize_of_runMeets (hA : BCHKS46At GF GE) (hk : kThree .two DK frRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    (meets : RunMeets (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty M₁ M₂ M₃ silK runK fx
      fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃')
    (L' : X' → E'.Str → Prop)
    (lang : ∀ rec y, L' (fx rec) (fy y) →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).coll y rec.1 ∨ (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).D y rec ≠ none)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃)))
    (held₁ : M₁.Held T.εs δ₁)
    (below₂ : Err.Below (Err.times (2 ^ T.depthReqT) (M₂.err δ₂)) T.εs)
    (held₃ : M₃.Held T.εs δ₃)
    (proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtFullSize T))
    (commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataWithFixedLinkAtFullSize T))
    (claim : A.Mat → List Token → List Token → Prop)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtFullSize T) claim) :
    SoundForWith (innerSystem (innerCompilerInputWithFixedLinkAtFullSize T)) (compiledIndexExtractor (soundnessAnalysisDataWithFixedLinkAtFullSize T)) claim
      (compiledSoundnessError (soundnessAnalysisDataWithFixedLinkAtFullSize T)) :=
  innerCompiledVerifierSoundWithFixedLinkAtFullSize_for hA hk wK dK wP dP
    ⟨keySoundOfFull_of_runMeets T M₁ M₂ M₃ fx fy acc' meets bl' er' rd' ok₁ ok₂ ok₃ δ₁ δ₂ δ₃ L'
      lang sound held₁ below₂ held₃, proofSound, commitment⟩ claim hs

end Full

/-! ## The small size -/

section Small
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecSmall} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsWithFixedLinkAtSmallSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtSmallSize A E DK DP runK runP rK rP depthReq early salt K P)
  {s₁' s₂' s₃' : Shape} (M₁ : Maps (DK.at srS.P.T.a).ds₁ s₁')
  (M₂ : Maps (DK.at srS.P.T.a).ds₂ s₂') (M₃ : Maps (DK.at srS.P.T.a).ds₃ s₃') {X' : Type}
  {E' : ExtSpec} (fx : RecSmall → X') (fy : (oneExternalString (2 ^ (DK.at srS.P.T.a).a) SgX).Str → E'.Str)
  (acc' : X' → E'.Str → Tr (s₁' ++ (s₂' ++ s₃')) → Bool)

/-- **The key file's named hypothesis on soundness at this size**, from nine premises: the law at
the key file's data and decision (`meets`); `Maps.OK` of the three lists of maps (`ok₁`, `ok₂`,
`ok₃`); a typed protocol's soundness (`sound`), which is shown nowhere here; the translation of the
languages (`lang`); three bounds on counts at T.εs (`held₁`, `below₂`, `held₃`). The law alone gives
nothing (`runMeets_top`). One call of `keySound_of_runMeets`. -/
theorem keySoundOfSmall_of_runMeets
    (meets : RunMeets (DK.at srS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty M₁ M₂ M₃ silK runK fx
      fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃')
    (L' : X' → E'.Str → Prop)
    (lang : ∀ rec y, L' (fx rec) (fy y) →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).coll y rec.1 ∨ (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).D y rec ≠ none)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃)))
    (held₁ : M₁.Held T.εs δ₁)
    (below₂ : Err.Below (Err.times (2 ^ T.depthReqT) (M₂.err δ₂)) T.εs)
    (held₃ : M₃.Held T.εs δ₃) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataWithFixedLinkAtSmallSize T) :=
  keySound_of_runMeets (lettersAt A (relationsAndEncodingOfClaims A E)) DK DP (front₀ rK) (join₀ rK) ByteArray.empty
    (front₀ rP) (join₀ rP) ByteArray.empty silK runK silP runP (entrySmallQ salt) (2 ^ depthReq)
    early none P T.letters T.names M₁ M₂ M₃ fx fy acc' meets bl' er' rd' ok₁ ok₂ ok₃ δ₁ δ₂ δ₃ L'
    lang sound held₁ below₂ held₃

/-- **The compiler's theorem at this size, for any claim, with the key file's hypothesis exchanged
for the nine premises of `keySoundOfSmall_of_runMeets`.** Left, all hypotheses of the theorem: these
nine (`meets`; `ok₁`, `ok₂`, `ok₃`; `lang`; `sound`, a typed protocol's soundness; `held₁`,
`below₂`, `held₃`); `proofSound`; `commitment`; the meaning (`hs`); the theorem on codes (`hA`) and
the five tests on numbers (`hk`, `wK`, `dK`, `wP`, `dP`) of `innerCompiledVerifierSoundWithFixedLinkAtSmallSize_for`; and, inside T,
hSeed and hε. Lean's list of axioms does not show them. Not in this list: the laws that stand in the
letters' types (T.m : `OracleCoding`, a coding one to one and onto; A.mat_cut): TwoSizesAt.lean's head. -/
theorem innerCompiledVerifierSoundWithFixedLinkAtSmallSize_of_runMeets (hA : BCHKS46At GF GE) (hk : kThree .two DK srRds DP ≤ K)
    (wK : DK.workFit = true) (dK : DK.depthFit = true) (wP : DP.workFit = true)
    (dP : DP.depthFit = true)
    (meets : RunMeets (DK.at srS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty M₁ M₂ M₃ silK runK fx
      fy acc')
    (bl' : OPos (s₁' ++ (s₂' ++ s₃')) → Bool)
    (er' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Finset E'.Pos)
    (rd' : X' → Rho (s₁' ++ (s₂' ++ s₃')) → Plains (s₁' ++ (s₂' ++ s₃')) →
      Finset (OPos (s₁' ++ (s₂' ++ s₃'))))
    (ok₁ : M₁.OK) (ok₂ : M₂.OK) (ok₃ : M₃.OK) (δ₁ : Err s₁') (δ₂ : Err s₂') (δ₃ : Err s₃')
    (L' : X' → E'.Str → Prop)
    (lang : ∀ rec y, L' (fx rec) (fy y) →
      (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).coll y rec.1 ∨ (DecR.configurationOfStoredTable A (relationsAndEncodingOfClaims A E)).D y rec ≠ none)
    (sound : (⟨s₁' ++ (s₂' ++ s₃'), bl', er', rd', acc'⟩ : InteractiveOracleProof X' E').Sound L'
      (Err.app δ₁ (Err.app δ₂ δ₃)))
    (held₁ : M₁.Held T.εs δ₁)
    (below₂ : Err.Below (Err.times (2 ^ T.depthReqT) (M₂.err δ₂)) T.εs)
    (held₃ : M₃.Held T.εs δ₃)
    (proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataWithFixedLinkAtSmallSize T))
    (commitment : CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataWithFixedLinkAtSmallSize T))
    (claim : A.Mat → List Token → List Token → Prop)
    (hs : CompilerSoundnessConditionStatements.soundFor (soundnessAnalysisDataWithFixedLinkAtSmallSize T) claim) :
    SoundForWith (innerSystem (innerCompilerInputWithFixedLinkAtSmallSize T)) (compiledIndexExtractor (soundnessAnalysisDataWithFixedLinkAtSmallSize T)) claim
      (compiledSoundnessError (soundnessAnalysisDataWithFixedLinkAtSmallSize T)) :=
  innerCompiledVerifierSoundWithFixedLinkAtSmallSize_for hA hk wK dK wP dP
    ⟨keySoundOfSmall_of_runMeets T M₁ M₂ M₃ fx fy acc' meets bl' er' rd' ok₁ ok₂ ok₃ δ₁ δ₂ δ₃ L'
      lang sound held₁ below₂ held₃, proofSound, commitment⟩ claim hs

end Small

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundWithFixedLinkAtFullSize_of_runMeets
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundWithFixedLinkAtSmallSize_of_runMeets
