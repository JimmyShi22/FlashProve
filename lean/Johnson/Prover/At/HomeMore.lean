-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/HomeMore.lean: two more premises of "the honest side is accepted" at the told
record of the goals' description with its number of coins laid anew (the letters of
Johnson/Prover/At/HomeAt.lean): the lengths of what is drawn, and the builder of an instance.

Main names.
  `drawFitB_of_good` (namespace `Johnson.Prover.Print`)   `drawFit_of_good`
      (Johnson/Prover/Print/DrawOfGood.lean) typed at the re-bound input, at the letters S:
      `DrawFit` from `GoodOwesB` at the plan's number of salt bytes and the lengths of the copy's
      leaves' salts
  `drawFit_home` (namespace `FlashProve`)   its call at `(flashProveDescription.reBound b).input Z allZeroDigest []`
  `build_tOf` (namespace `FlashProve`), `build_home`   the input's builder is `Flat.buildReq`
      (Johnson/Flat/LedgerClaim.lean): by unfolding
  `build_home_of_built`   so what `requestOfTokens` builds, the input's builder builds: the same
      request with the proof that it is well formed (`buildReq_of_built`, Johnson/Flat/BuiltOK.lean)

Limits. `GoodOwesB` is asked. Nothing on which requests `requestOfTokens` builds, nor on what an
index's matrix is. Nothing on soundness or completeness.

Local letters (notation of one section each). ℜ: the re-bound input InnerCompilerInput.reBound (R S c₀ m₀) n ·
  ℌ: the input Description.input (Description.reBound flashProveDescription b) Z allZeroDigest [].
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.PrintedBound
import Johnson.Prover.At.HomeAt
import Johnson.Prover.Print.DrawOfGood
import Johnson.Flat.BuiltOK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Johnson.Prover.Print
open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop (Dig)
open Rom (Bits)
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open LPFD.Full (saltG)
open OnBytes.Prover OnBytes.Prover.Print

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) (n : ℕ)

/-- the re-bound input -/
local notation "ℜ" => InnerCompilerInput.reBound (R S c₀ m₀) n

set_option maxRecDepth 20000 in
/-- **The lengths of what is drawn**, typed at the re-bound input. -/
theorem drawFitB_of_good {Kap : Type} (c : ByteArray) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)) (capT capL capB : ℕ → ℕ)
    (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap)
    (hG : GoodOwesB S c₀ m₀ n c (saltG S.G) sL bcT bcL bcB capT capL capB i r₁ s₁ d)
    (hs : ∀ j, j < (ℜ).protocol.wordLength → (d.s j).length = 256 + 8 * saltG S.G) : DrawFit (ℜ).queryLayout (ℜ).compilerParameters d :=
  drawFit_of_good S c₀ m₀ c sL bcT bcL bcB capT capL capB i r₁ s₁ d hG hs

end Johnson.Prover.Print

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles

theorem build_tOf {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c : Digest)
    (m : List (_root_.Iop.Dig 256)) : (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)).buildInstance = Flat.buildReq := by
  exact rfl

end FlashProve

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom (Bits)
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open LPFD.Full (saltG)
open OnBytes.Prover OnBytes.Prover.Print
open Johnson.Prover.Print

/- Lean compares these by their names (as in Johnson/Goal/Description/AtBound.lean). -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- the input there -/
local notation "ℌ" => Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []

set_option maxRecDepth 100000 in
/-- **The lengths of what is drawn, there.** -/
theorem drawFit_home {Kap : Type} (c : ByteArray) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits)) (capT capL capB : ℕ → ℕ)
    (i : (ℌ).Index) (r₁ : (ℌ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (d : Draw 256 (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap)
    (hG : GoodOwesB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) c (saltG (dataAtFiles flashProveData Z).G) sL bcT bcL bcB
      capT capL capB i r₁ s₁ d)
    (hs : ∀ j, j < (ℌ).protocol.wordLength → (d.s j).length = 256 + 8 * saltG (dataAtFiles flashProveData Z).G) :
    DrawFit (ℌ).queryLayout (ℌ).compilerParameters d :=
  drawFitB_of_good (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) c sL bcT bcL bcB capT capL capB i r₁ s₁ d hG hs

set_option maxRecDepth 100000 in
/-- The builder there is `Flat.buildReq`. -/
theorem build_home : (ℌ).buildInstance = Flat.buildReq := by exact rfl

set_option maxRecDepth 100000 in
/-- **What `requestOfTokens` builds, the builder there builds.** -/
theorem build_home_of_built {x' : List Token × List Token} {t : List Token}
    {x : Inst.Model.Instance Inst.Model.ppref} (h : requestOfTokens x' t = some x) :
    (ℌ).buildInstance x' t = some ⟨x, Flat.wellFormed_of_built h⟩ := by
  rw [build_home]
  exact Flat.buildReq_of_built h

end FlashProve
