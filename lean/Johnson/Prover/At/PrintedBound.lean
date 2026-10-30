-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/PrintedBound.lean: `printed_raw` (Johnson/Prover/At/PrintRaw.lean) over the input
and the told record with the number of coins laid anew (`InnerCompilerInput.reBound`, `LayoutsByPublicReading.reBound`,
Johnson/Goal/Conditions/ReBound.lean), at the letters S of the public files and a number n that is a
letter.

Why. The two inputs part in the number of coins alone, so every type and every field that is read
here is the same by unfolding. But Lean, asked to compare a field of the one with the same field of
the other at written public files, first compares the two inputs, and there it runs into the two
numbers. Here the passage is made once, at letters; whoever stands at the re-bound input calls these
names and compares like with like.

Main names (namespace `Johnson.Prover.Print`).
  `printB`       `printRaw`, typed at the re-bound input
  `GoodOwesB`    `GoodOwes` (Johnson/Prover/Print/FitsOfGood.lean), typed there
  `StratsOweB`   at each laying of the proof of three strings: `StratOwes`
      (Johnson/Prover/Print/OwesOf.lean) of the key file's and of the proof file's string
  `printed_bound`   `printed_raw` there, at a reading d₈ that is the pair
      (cAt Z hash, sevenAt Z hash), with the typed runs as `runsAt` (Johnson/Prover/Home/Defs.lean)

Limits. As `printed_raw`'s: each premise is asked, none is shown here. No probability. No goal is
stated. Nothing on soundness or completeness.

Local letters (notation of one section each). ℜ: the re-bound input: InnerCompilerInput.reBound (R S c₀ m₀) n,
  then InnerCompilerInput.reBound (R (S Z) c₀ m₀) n · 𝔗: the re-bound told record at Z, LayoutsByPublicReading.reBound
  (DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀) n.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.PrintRaw
import Johnson.Prover.Home.Defs
import Johnson.Goal.Conditions.ReBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open LPFD.Full (XF sBG sTG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

section One
variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) (n : ℕ)

/-- the re-bound input -/
local notation "ℜ" => InnerCompilerInput.reBound (R S c₀ m₀) n

/-- `printRaw`, typed at the re-bound input. -/
def printB {Kap : Type} (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap)
    (fb : FormBytes) (y : Raw 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) : FormBytes :=
  printRaw S c₀ m₀ i r₁ d fb y

/-- `GoodOwes`, typed at the re-bound input. -/
def GoodOwesB {Kap : Type} (c : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)) (capT capL capB : ℕ → ℕ)
    (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap) :
    Prop :=
  GoodOwes S c₀ m₀ c salt sL bcT bcL bcB capT capL capB i r₁ s₁ d

/-- At each laying of the proof of three strings: what is asked of the two strategies. -/
def StratsOweB (bcT bcB : ByteCoins (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits))
    (π : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) (k : ℕ) (c₂ : Dig 256) (r₂ : (ℜ).protocol.Rec) : Prop :=
  ∀ (πT : OneProtocolProof 256 (QT S)) (πL : OneProtocolProof 256 (QL S)) (πB : OneProtocolProof 256 (QB S)),
    π = ⟨k, some πT, (c₂, r₂, some πL), some πB⟩ →
    StratOwes (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
        silK S.runK bcT πT ∧
      StratOwes (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
        silP S.runP bcB πB

end One

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)
  (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) (n : ℕ) (hash : VerifiableInference.Hash)

/-- the re-bound told record at Z -/
local notation "𝔗" => LayoutsByPublicReading.reBound (DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀) n
/-- the re-bound input -/
local notation "ℜ" => InnerCompilerInput.reBound (R (S Z) c₀ m₀) n

set_option maxRecDepth 20000 in
/-- **Where the typed runs yield a proof, verify says yes to the printed form**: over the re-bound
input and told record. -/
theorem printed_bound {Kap : Type} (d₈ : (𝔗).D) (hd : d₈ = (cAt Z hash, sevenAt Z hash))
    (scope : VerifierAndGoals.InScope Z = true) (prompt output : List Token)
    (b₀ : (ℜ).LeafBody) (st : Strats (ℜ).protocol Kap) (capT capL capB : ℕ → ℕ)
    (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : (ℜ).Instance)
    (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap) (π : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (e₁ e₂ : (ℜ).protocol.OutOfDomainSeed) (τT : Tr (ℜ).protocol.offline.shape) (τL : Tr (ℜ).protocol.link.shape)
    (τB : Tr (ℜ).protocol.onlineBatch.loc.shape) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (typedOracleCarrier (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)) (fb : FormBytes)
    (hS : PublicS (S Z)) (hN : NumbersFit (KF (S Z).DK (S Z).DP) (S Z).DK dsF (S Z).DP)
    (hp : pack i d ((runsAt 𝔗 b₀ st capT capL capB d₈ (i, r₁, s₁) x d).det
      (readBlocks ((𝔗).m d₈) (famOne hash))) = .ok (π, e₁, e₂, τT, τL, τB))
    (hE : Ends (ℜ).queryLayout ((𝔗).Sd d₈) ((𝔗).cA d₈) (ℜ).fixedSample b₀ st capT capL capB
      (readBlocks ((𝔗).m d₈) (famOne hash)) i r₁ s₁ x d π e₁ e₂ τT τL τB)
    (aT : (ℜ).protocol.offline.accept ((ℜ).protocol.recOf i r₁ e₁) ((ℜ).protocol.encodeIndex i r₁) τT = true)
    (aB : (ℜ).protocol.onlineBatch.loc.accept (x, (ℜ).protocol.recOf i d.r e₂) ((ℜ).protocol.encodeIndex i d.r) τB = true)
    (hG : GoodOwesB (S Z) c₀ m₀ n (digToBytes (cAt Z hash)) salt sL bcT bcL bcB capT capL capB i r₁
      s₁ d)
    (hσ : StratsOweB (S Z) c₀ m₀ n bcT bcB π d.n
      ((committerTreeKeptByProver (ℜ).queryLayout b₀ ((ℜ).protocol.encodeIndex i d.r) d.s).det (readBlocks ((𝔗).m d₈) (famOne hash))).root
      ((ℜ).protocol.recOf i d.r e₂))
    (hn : ((𝔗).Sd d₈).num d.n τB.plains = true)
    (hb : (ℜ).buildInstance (prompt, output) [] = some x)
    (hv : (verifyAtKeyRoot (ℜ).queryLayout ((𝔗).Sd d₈) ((𝔗).cA d₈) (ℜ).fixedSample (ℜ).compilerParameters
      ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd d₈) b₀ i r₁ s₁).det (readBlocks ((𝔗).m d₈) (famOne hash))).1 x π).det
        (readBlocks ((𝔗).m d₈) (famOne hash)) = true) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z)
      (ZKCP.digestUnder hash (𝔗).encT ((𝔗).part d₈,
        ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd d₈) b₀ i r₁ s₁).det (readBlocks ((𝔗).m d₈) (famOne hash))).1))
      prompt output
      (printB (S Z) c₀ m₀ n i r₁ d fb ((runsAt 𝔗 b₀ st capT capL capB d₈ (i, r₁, s₁) x d).det
        (readBlocks ((𝔗).m d₈) (famOne hash))))).evaluate hash = true := by
  subst hd
  exact printed_raw S f₀ Hb c₀ m₀ Z hash scope prompt output b₀ st capT capL capB i r₁ s₁ x d π e₁
    e₂ τT τL τB salt sL bcT bcL bcB fb hS hN hp hE aT aB hG hσ hn hb hv

end Johnson.Prover.Print
