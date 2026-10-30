-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/WiresAt.lean: at the input of the full size (`innerCompilerInputAtFullSize`,
Johnson/Flat/Dec/TwoSizesAt.lean) the three protocols and the three wire records of the compiled
verifiers are the written ones: those of a whole written file (`wholeDesc`, `wqWhole`,
OnBytes/Maker/) and of the written link (`linkSkeletonOfRoundData`, OnBytes/Flat/LinkSib.lean; `wqW`,
Johnson/RunOne/StrictLinkW.lean). Each by unfolding alone.

Why. The compiled prover's theorem stands at the letters of `verifyOfflineProof`, `verifyLinkProof`, `verifyOnlineProof` of any wiring W
(Johnson/Prover/YesOfProve.lean). What is shown of the prover's strings at written files (that they
can be printed, that a search's numbers are written apart, that a round has few trees) stands at
`wqWhole`, `wqW` and the written protocols. These equations say that at the goals' description both
are one term.

Main names (namespace `VerifiableInference.OnPublicFiles`; T is any `InnerCompilerInputAndAnalysisFieldsAtFullSize`: all data of the
three files are variables).
  `batTC_fullD`, `bat_fullD`, `batLC_fullD`   the three protocols
  `wTC_fullD`, `wBC_fullD`, `wLC_fullD`       the three wire records
  `K_fullD`, `depth_fullD`, `depthReq_fullD`, `depthReqT_fullD`, `depthReqL_fullD`, `p_fullD`: the
      numbers
  `proveTA_fullD`, `proveLA_fullD`, `proveBA_fullD`   the compiled prover at the verifiers' letters
      is the compiled prover at the written letters
  `p_tOf`, `sMT_tOf`, `sFS_tOf` (namespace `FlashProve`)   at the letters S of one set of public
      files: the compiler's two lengths: 256 + 8 times the plan's number of salt bytes, and 256

Kin in the library. `FlashProve.depthReqT_tOf`, `sBG_logLeaves`
(Johnson/Goal/Conditions/DepthsAtDescriptionDataAtFiles.lean) and `depth_at` (Johnson/Top/Fire/Code/TieAtValues.lean):
the two request depths at S; they are not said again. `depthD`, `wireKD`
(Johnson/Goal/Conditions/BindsLetters.lean): `depth_fullD` and `K_fullD` at one family of letters.
`bat_full`, `test_full` (Johnson/TypedOracleCompiler/Joined/FieldsAtSizes.lean [not in this library]): the like at the object that is made
of a plan's own data; from there the habit `by exact rfl`.

Limits. Equations between terms of this library, each proved by `rfl`. No premise: they hold at all
public files. Nothing says that a law of the wires holds, that a verifier says yes, or what the maps
from symbols to leaves' bodies are. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.TwoSizesAt
import Johnson.RunOne.StrictLinkVLA
import Johnson.Goal.Tie.DescriptionOnDecodedProof
import Johnson.Prover.YesOfProve

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Johnson.RunOne.StrictW (wqW)
open OnBytes.Prover (proveX TreeK Coins Res)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-! ## The three protocols -/

theorem batTC_fullD : batTC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).offlineRoundSplits =
    (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK
      runK).batch := by
  exact rfl

theorem bat_fullD : (innerCompilerInputAtFullSize T).protocol.onlineBatch =
    (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP).batch := by
  exact rfl

theorem batLC_fullD : batLC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).linkRoundSplits =
    (linkSkeletonOfRoundData (ckP .two) ds frS.P.T.a xs dec).up := by exact rfl

/-! ## The three wire records -/

theorem wTC_fullD : wTC (innerCompilerInputAtFullSize T).queryLayout =
    wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
      silK runK := by exact rfl

theorem wBC_fullD : wBC (innerCompilerInputAtFullSize T).queryLayout =
    wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
      silP runP := by exact rfl

theorem wLC_fullD : wLC (innerCompilerInputAtFullSize T).queryLayout =
    wqW (ckP .two) ds frS.P.T.a xs dec K (chalP .two K) := by exact rfl

/-! ## The numbers -/

theorem K_fullD : (innerCompilerInputAtFullSize T).queryLayout.K = K + 1 := by exact rfl
theorem depth_fullD : (innerCompilerInputAtFullSize T).queryLayout.depth = frS.P.T.a := by exact rfl
theorem depthReq_fullD : (innerCompilerInputAtFullSize T).queryLayout.depthReq = depthReq := by exact rfl
theorem depthReqT_fullD : (innerCompilerInputAtFullSize T).queryLayout.depthReqT = T.depthReqT := by exact rfl
theorem depthReqL_fullD : (innerCompilerInputAtFullSize T).queryLayout.depthReqL = 0 := by exact rfl
theorem p_fullD : (innerCompilerInputAtFullSize T).compilerParameters = T.p := by exact rfl

/-! ## The compiled prover -/

section
variable (cA : (innerCompilerInputAtFullSize T).protocol.OutOfDomainAnswer → List (Dig 256)) (r₀ : (innerCompilerInputAtFullSize T).protocol.Rec)
  (xt : ℕ → TreeK 256 (typedOracleCarrier (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).LeafBody (innerCompilerInputAtFullSize T).offlineRoundSplits
    (innerCompilerInputAtFullSize T).linkRoundSplits))
  (co : Coins 256 (typedOracleCarrier (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).LeafBody (innerCompilerInputAtFullSize T).offlineRoundSplits
    (innerCompilerInputAtFullSize T).linkRoundSplits)) (cap : ℕ → ℕ)

/-- The key file's: the compiled prover at `verifyOfflineProof`'s letters is the one at the written file's. -/
theorem proveTA_fullD (cm : Dig 256) (rec : (innerCompilerInputAtFullSize T).protocol.Rec)
    (y : (oneExternalString (innerCompilerInputAtFullSize T).protocol.wordLength (innerCompilerInputAtFullSize T).protocol.Symbol).Str)
    (σ : Strat (innerCompilerInputAtFullSize T).protocol.offline.shape Unit) :
    proveTA (innerCompilerInputAtFullSize T).queryLayout cA xt co cap cm rec y σ =
      proveX Tag.test
        (wholeDesc (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK
          runK).batch
        (wqWhole (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
          ByteArray.empty silK runK)
        (innerCompilerInputAtFullSize T).queryLayout.embT id (fun _ => none) (cmsTA cA cm rec.2) rec y xt σ co cap := by
  exact rfl

/-- The entry file's. -/
theorem proveLA_fullD (cm cm' : Dig 256) (rec rec' : (innerCompilerInputAtFullSize T).protocol.Rec)
    (y : (twoExternalStrings (innerCompilerInputAtFullSize T).protocol.wordLength (innerCompilerInputAtFullSize T).protocol.Symbol).Str)
    (σ : Strat (innerCompilerInputAtFullSize T).protocol.link.shape Unit) :
    proveLA (innerCompilerInputAtFullSize T).queryLayout cA xt co cap cm cm' rec rec' y σ =
      proveX Tag.link (linkSkeletonOfRoundData (ckP .two) ds frS.P.T.a xs dec).up
        (wqW (ckP .two) ds frS.P.T.a xs dec K (chalP .two K))
        (innerCompilerInputAtFullSize T).queryLayout.embL id (fun _ => none) (cmsLA cA cm cm' rec.2 rec'.2) (rec, rec') y
        xt σ co cap := by exact rfl

/-- The proof file's. -/
theorem proveBA_fullD (cm : Dig 256) (x : X) (rec : (innerCompilerInputAtFullSize T).protocol.Rec)
    (y : (oneExternalString (innerCompilerInputAtFullSize T).protocol.wordLength (innerCompilerInputAtFullSize T).protocol.Symbol).Str)
    (σ : Strat (innerCompilerInputAtFullSize T).protocol.onlineBatch.loc.shape Unit) :
    proveBA (innerCompilerInputAtFullSize T).queryLayout cA r₀ xt co cap cm x rec y σ =
      proveX Tag.onl
        (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
          runP).batch
        (wqWhole (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
          ByteArray.empty silP runP)
        (innerCompilerInputAtFullSize T).queryLayout.embB id (xinBA r₀) (cmsBA cA cm rec.2) (x, rec) y xt σ co cap := by
  exact rfl

end

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open LPFD.Full (sBG sTG saltG KF)

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c : Digest) (m : List (_root_.Iop.Dig 256))

theorem p_tOf : (S.inputFieldsAtReadings c m).p = LPFD.Full.pAt (saltG S.G) := by exact rfl
theorem sMT_tOf : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).compilerParameters.sMT = 256 + 8 * saltG S.G := by exact rfl
theorem sFS_tOf : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).compilerParameters.sFS = 256 := by exact rfl

end FlashProve
