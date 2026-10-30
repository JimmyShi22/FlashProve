-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/PrintedHome.lean: `printed_bound` (Johnson/Prover/At/PrintedBound.lean) at the
told record of the goals' description with its number of coins laid anew
(`((theTerms placeHolderCoins).T Z).reBound (b Z)` over `(flashProveDescription.reBound b).input Z allZeroDigest []`, b a
letter; Johnson/Prover/At/HomeAt.lean), at the goals' verify at `flashProveDescription` with its own parser.

Main names (namespace `FlashProve`).
  `printed_home`   where the typed runs at the reading d₈ (`runsAt`, Johnson/Prover/Home/Defs.lean)
      yield a proof, d₈ the pair (cAt Z hash, sevenAt Z hash): under `Ends`, the key file's and the
      proof file's accepts, the yes of the test of the copy's number, the compiled verifier's yes at
      the committer's own key, and four named premises (PublicS · `GoodOwesB` · `StratsOweB` · the
      instance is built): verify evaluates to true at the commitment
      `digestUnder hash T.encT (T.part d₈, key)` and at the form `printB … y`

Limits. As `printed_raw`'s (Johnson/Prover/At/PrintRaw.lean). The tests on public numbers are paid
(`numbersFit_the`); the four named premises are asked. No probability. No goal is stated. Nothing on
soundness or completeness.

Local letters (notation of this file alone). ℌ: the input Description.input (Description.reBound flashProveDescription
  b) Z allZeroDigest [] · 𝔗: the told record LayoutsByPublicReading.reBound (HonestTerms.T (theTerms placeHolderCoins) Z)
  (b Z).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.PrintedBound
import Johnson.Prover.At.HomeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.Prover.Print
open Johnson.Prover.Print

/- Lean compares these by their names (as in Johnson/Goal/Description/AtBound.lean). -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- the input there -/
local notation "ℌ" => Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []
/-- the told record there -/
local notation "𝔗" => LayoutsByPublicReading.reBound (HonestTerms.T (theTerms placeHolderCoins) Z) (b Z)

set_option maxRecDepth 100000 in
/-- **Where the typed runs yield a proof, verify says yes to the printed form.** -/
theorem printed_home {Kap : Type} (hash : VerifiableInference.Hash) (d₈ : (𝔗).D)
    (hd : d₈ = (cAt Z hash, sevenAt Z hash)) (scope : VerifierAndGoals.InScope Z = true)
    (prompt output : List Token) (b₀ : (ℌ).LeafBody) (st : Strats (ℌ).protocol Kap) (capT capL capB : ℕ → ℕ)
    (i : (ℌ).Index) (r₁ : (ℌ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : (ℌ).Instance)
    (d : Draw 256 (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap) (π : OfflineLinkOnlineProof 256 (ℌ).protocol (ℌ).offlineRoundSplits (ℌ).linkRoundSplits)
    (e₁ e₂ : (ℌ).protocol.OutOfDomainSeed) (τT : Tr (ℌ).protocol.offline.shape) (τL : Tr (ℌ).protocol.link.shape)
    (τB : Tr (ℌ).protocol.onlineBatch.loc.shape) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits)) (fb : FormBytes)
    (hS : PublicS (dataAtFiles flashProveData Z))
    (hp : pack i d ((runsAt 𝔗 b₀ st capT capL capB d₈ (i, r₁, s₁) x d).det
      (readBlocks ((𝔗).m d₈) (famOne hash))) = .ok (π, e₁, e₂, τT, τL, τB))
    (hE : Ends (ℌ).queryLayout ((𝔗).Sd d₈) ((𝔗).cA d₈) (ℌ).fixedSample b₀ st capT capL capB
      (readBlocks ((𝔗).m d₈) (famOne hash)) i r₁ s₁ x d π e₁ e₂ τT τL τB)
    (aT : (ℌ).protocol.offline.accept ((ℌ).protocol.recOf i r₁ e₁) ((ℌ).protocol.encodeIndex i r₁) τT = true)
    (aB : (ℌ).protocol.onlineBatch.loc.accept (x, (ℌ).protocol.recOf i d.r e₂) ((ℌ).protocol.encodeIndex i d.r) τB = true)
    (hG : GoodOwesB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) (digToBytes (cAt Z hash)) salt sL bcT bcL bcB
      capT capL capB i r₁ s₁ d)
    (hσ : StratsOweB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) bcT bcB π d.n
      ((committerTreeKeptByProver (ℌ).queryLayout b₀ ((ℌ).protocol.encodeIndex i d.r) d.s).det (readBlocks ((𝔗).m d₈) (famOne hash))).root
      ((ℌ).protocol.recOf i d.r e₂))
    (hn : ((𝔗).Sd d₈).num d.n τB.plains = true)
    (hb : (ℌ).buildInstance (prompt, output) [] = some x)
    (hv : (verifyAtKeyRoot (ℌ).queryLayout ((𝔗).Sd d₈) ((𝔗).cA d₈) (ℌ).fixedSample (ℌ).compilerParameters
      ((committerAtFixedCoins (ℌ).queryLayout ((𝔗).Sd d₈) b₀ i r₁ s₁).det (readBlocks ((𝔗).m d₈) (famOne hash))).1 x π).det
        (readBlocks ((𝔗).m d₈) (famOne hash)) = true) :
    (VerifierAndGoals.verify flashProveDescription Z (flashProveDescription.parse Z)
      (ZKCP.digestUnder hash (𝔗).encT ((𝔗).part d₈,
        ((committerAtFixedCoins (ℌ).queryLayout ((𝔗).Sd d₈) b₀ i r₁ s₁).det (readBlocks ((𝔗).m d₈) (famOne hash))).1))
      prompt output
      (printB (dataAtFiles flashProveData Z) allZeroDigest [] (b Z) i r₁ d fb
        ((runsAt 𝔗 b₀ st capT capL capB d₈ (i, r₁, s₁) x d).det
          (readBlocks ((𝔗).m d₈) (famOne hash))))).evaluate hash = true :=
  printed_bound (dataAtFiles flashProveData) flashProveData.f₀ flashProveData.honest allZeroDigest [] Z (b Z) hash d₈ hd scope prompt
    output b₀ st capT capL capB i r₁ s₁ x d π e₁ e₂ τT τL τB salt sL bcT bcL bcB fb hS
    (Meaning.numbersFit_the Z) hp hE aT aB hG hσ hn hb hv

end FlashProve
