-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/StratsAt.lean: what `printed_bound` and `printed_home`
(Johnson/Prover/At/PrintedBound.lean, PrintedHome.lean) ask of the two strategies, `StratsOweB`,
from a law on each strategy's own run (`StratLaw`, Johnson/Prover/Print/StratLaw.lean) and what the
prover of a whole request returns (`Ends`, Johnson/Prover/All/Good.lean).

Main names.
  `stratsOwe_fullD` (namespace `VerifiableInference.OnPublicFiles`)   for all data, at the input of the
      full size, at any seeds' record and answers' code: `Ends` · `StratLaw` of the key file's
      strategy at bcT's two run values · `StratLaw` of the proof file's at bcB's: then at each
      laying of the proof of three strings: `StratOwes` of the key file's and of the proof file's
      string
  `stratsOweB_of_laws` (namespace `Johnson.Prover.Print`)   the same as `StratsOweB`, at the letters
      S, typed at the re-bound input

By: `Ends.fields`, `proveTA_fullD`, `proveBA_fullD` (Johnson/Prover/At/WiresAt.lean),
`stratOwes_of_law`, `prf_inj` (Johnson/Prover/At/PrintRaw.lean).

Limits. That a strategy meets `StratLaw` is asked, not shown here (an idle strategy meets it:
stratLaw_idle, Johnson/Prover/Print/IdleStrat.lean); the two strategies are those at the seeds e₁,
e₂ and the draw's own coins. Nothing on acceptance, soundness or completeness.

Local letters (notation of one section each). 𝔯: the input innerCompilerInputAtFullSize T · ℜ: the re-bound input
  InnerCompilerInput.reBound (R S c₀ m₀) n.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.PrintedBound
import Johnson.Prover.Print.StratLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.Prover.Print
open Johnson.Prover.Print (StratOwes StratLaw stratOwes_of_law)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- the input -/
local notation "𝔯" => innerCompilerInputAtFullSize T

set_option maxRecDepth 20000 in
/-- **What is asked of the two strategies, from a law on each one's own run.** For all data. -/
theorem stratsOwe_fullD {Kap : Type} (Sd : OutOfDomainSampleQueryLayout 256 (𝔯).queryLayout.K (𝔯).protocol (𝔯).LeafBody (𝔯).offlineRoundSplits (𝔯).linkRoundSplits)
    (cA : (𝔯).protocol.OutOfDomainAnswer → List (Dig 256)) (b₀ : (𝔯).LeafBody) (st : Strats (𝔯).protocol Kap)
    (capT capL capB : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (𝔯).queryLayout.K (typedOracleCarrier (𝔯).protocol (𝔯).LeafBody (𝔯).offlineRoundSplits (𝔯).linkRoundSplits)))
    (i : (𝔯).Index) (r₁ : (𝔯).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : (𝔯).Instance)
    (d : Draw 256 (𝔯).protocol (𝔯).LeafBody (𝔯).offlineRoundSplits (𝔯).linkRoundSplits Kap) (π : OfflineLinkOnlineProof 256 (𝔯).protocol (𝔯).offlineRoundSplits (𝔯).linkRoundSplits)
    (e₁ e₂ : (𝔯).protocol.OutOfDomainSeed) (τT : Tr (𝔯).protocol.offline.shape) (τL : Tr (𝔯).protocol.link.shape)
    (τB : Tr (𝔯).protocol.onlineBatch.loc.shape)
    (bcT bcB : ByteCoins (typedOracleCarrier (𝔯).protocol (𝔯).LeafBody (𝔯).offlineRoundSplits (𝔯).linkRoundSplits))
    (hE : Ends (𝔯).queryLayout Sd cA (𝔯).fixedSample b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB)
    (lT : StratLaw (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
      (st.T i r₁ e₁ d.κ) bcT.run2 bcT.run3)
    (lB : StratLaw (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
      (st.B i d.r e₂ x d.n d.κ) bcB.run2 bcB.run3)
    (k : ℕ) (c₂ : Dig 256) (r₂ : (𝔯).protocol.Rec) (πT : OneProtocolProof 256 (batTC (𝔯).protocol (𝔯).offlineRoundSplits))
    (πL : OneProtocolProof 256 (batLC (𝔯).protocol (𝔯).linkRoundSplits)) (πB : OneProtocolProof 256 (𝔯).protocol.onlineBatch)
    (hπ : π = ⟨k, some πT, (c₂, r₂, some πL), some πB⟩) :
    StratOwes (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty silK runK bcT
        πT ∧
      StratOwes (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP runP bcB
        πB := by
  obtain ⟨πT₀, πL₀, πB₀, hπ₀, rT, -, rB, -, -, -⟩ := hE.fields
  obtain ⟨rfl, -, rfl, -⟩ := prf_inj (hπ₀.symm.trans hπ)
  rw [proveTA_fullD] at rT
  rw [proveBA_fullD] at rB
  exact ⟨stratOwes_of_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rT lT,
    stratOwes_of_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rB lB⟩

end VerifiableInference.OnPublicFiles

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.Prover.Print

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) (n : ℕ)

/-- the re-bound input -/
local notation "ℜ" => InnerCompilerInput.reBound (R S c₀ m₀) n

set_option maxRecDepth 20000 in
/-- **`StratsOweB` from a law on each strategy's own run.** -/
theorem stratsOweB_of_laws {Kap : Type} (Sd : OutOfDomainSampleQueryLayout 256 (ℜ).queryLayout.K (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (cA : (ℜ).protocol.OutOfDomainAnswer → List (Dig 256)) (b₀ : (ℜ).LeafBody) (st : Strats (ℜ).protocol Kap)
    (capT capL capB : ℕ → ℕ) (g : Fam (typedOracleFamily 256 (ℜ).queryLayout.K (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)))
    (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : (ℜ).Instance)
    (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap) (π : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (e₁ e₂ : (ℜ).protocol.OutOfDomainSeed) (τT : Tr (ℜ).protocol.offline.shape) (τL : Tr (ℜ).protocol.link.shape)
    (τB : Tr (ℜ).protocol.onlineBatch.loc.shape)
    (bcT bcB : ByteCoins (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits))
    (hE : Ends (ℜ).queryLayout Sd cA (ℜ).fixedSample b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB)
    (lT : StratLaw (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀)
      ByteArray.empty (st.T i r₁ e₁ d.κ) bcT.run2 bcT.run3)
    (lB : StratLaw (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty (st.B i d.r e₂ x d.n d.κ) bcB.run2 bcB.run3)
    (k : ℕ) (c₂ : Dig 256) (r₂ : (ℜ).protocol.Rec) : StratsOweB S c₀ m₀ n bcT bcB π k c₂ r₂ :=
  fun πT πL πB hπ => stratsOwe_fullD (S.inputFieldsAtReadings c₀ m₀) Sd cA b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂
    τT τL τB bcT bcB hE lT lB k c₂ r₂ πT πL πB hπ

end Johnson.Prover.Print
