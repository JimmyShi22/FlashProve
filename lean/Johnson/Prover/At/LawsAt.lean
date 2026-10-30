-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/LawsAt.lean: what the compiled prover's theorem at the three verifiers
(`vTA_yes_of_prove`, `vLA_yes_of_prove`, `vBA_yes_of_prove`, Johnson/Prover/YesOfProve.lean) asks of
wires and marks, at the input of the full size (`innerCompilerInputAtFullSize`,
Johnson/Flat/Dec/TwoSizesAt.lean): calls of what stands in the library.

Main names (namespace `VerifiableInference.OnPublicFiles`; T is any `InnerCompilerInputAndAnalysisFieldsAtFullSize`: all data of the
three files are variables).
  `oka_fullD`      `OKA` (the four laws of the wires, and the answers' code) under the six tests on
      numbers of `wires_fullD`, the entry file's four as one `EntryFit`
  `keyFmt_fullD`, `entryFmt_fullD`, `proofFmt_fullD`   every round of the three files' marks has a
      format
  `num_fullD`      where the letters' test of the copy's number is `numCopy`: it says yes at a proof
      file's string whose front bears that number
  `num_tOf` (namespace `FlashProve`)   at the letters S of one set of public files it is `numCopy`

Kin in the library, not said again: that the three verifiers are local and the three files' marks
coherent: `keyLocal_fullD`, `entryLocal_fullD`, `proofLocal_fullD`, `keyCoherent_fullD`,
`entryCoherent_fullD`, `proofCoherent_fullD` (Johnson/Flat/Dec/ElevenAt.lean): each unfolds to the
premise that the prover's theorem asks.

Limits. The six tests on numbers are premises here: that the data of a set of public files meet them
is not shown here. Nothing says that a verifier says yes. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.WiresAt
import Johnson.Flat.Dec.ElevenAt
import Johnson.Flat.Dec.EntrySound
import Johnson.Top.Fire.Code.PvFrontNum
import OnBytes.Maker.WholeLaws
import Compile.Joined.Ann
import Iop.BatchFmt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Joined (pls₁)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- **The laws of the wires and of the answers' code**, under the tests on numbers. -/
theorem oka_fullD (hk : kThree .two DK [] DP ≤ K) (hE : EntryFit K ds) (wK : DK.workFit = true)
    (dK : DK.depthFit = true) (wP : DP.workFit = true) (dP : DP.depthFit = true) :
    OKA (innerCompilerInputAtFullSize T).queryLayout (innerCompilerInputAtFullSize T).answerCode :=
  have w := wires_fullD T hk hE.bL hE.wLk hE.own hE.dL wK dK wP dP
  ⟨w.1, w.2.1, w.2.2.1, w.2.2.2, ⟨answersCode_fullD T, answersLength_fullD T⟩⟩

/-- Every round of the key file's marks has a format. -/
theorem keyFmt_fullD : (innerCompilerInputAtFullSize T).offlineRoundSplits.Fmt :=
  Compile.Joined.Chains.ann_fmt _
    (chainsOf_laws (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty)

/-- The entry file's. -/
theorem entryFmt_fullD : (innerCompilerInputAtFullSize T).linkRoundSplits.Fmt := by
  show (_root_.Run.Twin.allLo (TypedOracleCompiler.Run.PQ.SOf (ckP .two) ds)).Fmt
  rw [_root_.Run.Twin.allLo_eq]
  exact RoundSplits.fmt_allLocal _

/-- The proof file's. -/
theorem proofFmt_fullD : (innerCompilerInputAtFullSize T).protocol.onlineBatch.ann.Fmt :=
  Compile.Joined.Chains.ann_fmt _
    (chainsOf_laws (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty)

/-- **The test of the copy's number says yes** at a string whose front bears that number. -/
theorem num_fullD (hn : T.num = PV.Front.numCopy) (copy : ℕ)
    (π : OneProtocolProof 256 (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
                  silP runP).batch)
    (h : (pls₁ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP) π).1.copy = copy) :
    (innerCompilerInputAtFullSize T).seedQueries.num copy π.plains = true := by
  show T.num copy π.plains = true
  rw [hn]
  exact decide_eq_true h

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c : Digest) (m : List (_root_.Iop.Dig 256))

theorem num_tOf : (S.inputFieldsAtReadings c m).num = PV.Front.numCopy := by exact rfl

end FlashProve
