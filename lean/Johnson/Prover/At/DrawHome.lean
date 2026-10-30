-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/DrawHome.lean: at the written draw (`drawAt`, Johnson/Prover/Print/DrawOwes.lean),
at every raw value: `GoodOwesB` (Johnson/Prover/At/PrintedBound.lean) and `DrawFit`
(Johnson/Prover/All/Yes.lean): at the letters S of the public files over the re-bound input, and at
the goals' description (`(flashProveDescription.reBound b).input Z allZeroDigest []`, b a letter).

Main names.
  `drawK κOf N c x` (namespace `Johnson.Prover.Print`)   `drawAt` at the maker
      fun k r => κOf (k, r): the interactive provers' coins are κOf of the raw κ₀ and the four run
      values of the two tidy byte coins (`drawK_κ`, rfl)
  `drawOwes_drawK`   the record on the draw (`DrawOwes`) at it, its clause "same" with it, under the
      tie: runs (κOf (k, r)) = r at every r of four strings of 32 bytes, none of them 32 zero bytes
      (`Runs4.Fit`)
  `goodOwes_anyMk`, `drawFit_anyMk`   `GoodOwes` and `DrawFit` at the written draw do not hang on
      the maker of the interactive provers' coins
  `maxDepthW_lt`, `maxDepthL_lt`   a whole file's and the entry file's greatest depths are below
      2^64 where no tree is deeper than 63 and the stored tables' depth is below 64
  `publicOwes_of`   `PublicOwes` (Johnson/Prover/Print/DrawAtS.lean) from `NumbersFit`, the two
      files' widths and the three caps
  `goodOwesB_drawK`, `drawFitB_drawK`   at the letters S, typed at the re-bound input
  `good_home`, `drawFit_drawK_home` (namespace `FlashProve`)   at the goals' description: the first
      in scope and under protocolDataWellFormed, with caps below 2^64; the second under `saltG ≤ 64` alone
  `same_home`   under the tie and `saltG ≤ 64`: runs at the written draw's coins gives the four run
      values of the two tidy byte coins
  `part_home`   the told part of the pair (cAt Z hash, sevenAt Z hash) is cAt Z hash (rfl)

Paid at the description: the coding (`honestEnc_the`), the depths (`numbersFit_the`,
`publicL_full`), the widths and the number of salt bytes (`sizesSay_the`,
Johnson/Goal/Meaning/WordsFitAtThe.lean).

Limits. The tie is a premise of `drawOwes_drawK` and `same_home` alone. It makes r ↦ κOf (k, r) one
to one on the fitting r: so it can be met only at coins with at least as many values as these
(nearly 2^1024); that such coins are laid is not shown here (types and two maps: tie_toy,
Johnson/Goal/Conditions/HomeTieMet.lean). The four ends take no tie. Asked: c has 32 bytes; the
entry's binding shape has depth 0; the key's leaves' own salts have at most 64 bytes; the caps. That
a strategy sends the run values that its coins hold is not said here. Nothing on how any program
draws the raw value, and nothing is said of its distribution. Nothing on soundness or completeness.

Local letters (notation of one section each). ℜ: the re-bound input InnerCompilerInput.reBound (R S c₀ m₀) n ·
  ℌ: the input Description.input (Description.reBound flashProveDescription b) Z allZeroDigest [] · 𝔖: the letters of the
  public files, dataAtFiles flashProveData Z.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.HomeMore
import Johnson.Prover.Print.DrawAtS
import Johnson.Goal.Meaning.WordsFitAtThe
import Johnson.Flat.Dec.FitAtWritten

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
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF)
open Johnson.Prover.At (HonestEnc)
open OnBytes.Prover OnBytes.Prover.Print

section Gen
variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  {Kap₀ Kap : Type}

/-- **The written draw at the maker fun k r => κOf (k, r).** -/
def drawK (κOf : Kap₀ × Runs4 → Kap) (N : DrawNums) (c : ByteArray)
    (x : DrawRaw L Bd aT aL Kap₀) : Draw 256 L Bd aT aL Kap :=
  drawAt (fun k r => κOf (k, r)) N c x

/-- Its κ: κOf of the raw κ₀ and the four run values of the two tidy byte coins. -/
theorem drawK_κ (κOf : Kap₀ × Runs4 → Kap) (N : DrawNums) (c : ByteArray)
    (x : DrawRaw L Bd aT aL Kap₀) :
    (drawK κOf N c x).κ = κOf (x.κ₀, (((x.bT.tidy N.salt N.sT).run2, (x.bT.tidy N.salt N.sT).run3),
      ((x.bB.tidy N.salt N.sB).run2, (x.bB.tidy N.salt N.sB).run3))) := rfl

/-- **The record on the draw, at every raw value**, its clause "same" with it: under the tie of the
coins to the run values, asked at the values that occur (`Runs4.Fit`). -/
theorem drawOwes_drawK (κOf : Kap₀ × Runs4 → Kap) (runs : Kap → Runs4)
    (hκ : ∀ k r, Runs4.Fit r → runs (κOf (k, r)) = r) (N : DrawNums) (c : ByteArray)
    (x : DrawRaw L Bd aT aL Kap₀) (h : N.salt ≤ 64) :
    DrawOwes N c runs (x.bT.tidy N.salt N.sT) (x.bL.tidy N.salt N.sL) (x.bB.tidy N.salt N.sB)
      (drawK κOf N c x) :=
  drawOwes_drawAt (fun k r => κOf (k, r)) runs hκ N c x h

end Gen

/-! ## Depths -/

/-- A whole file's greatest depth. -/
theorem maxDepthW_lt (D : WholeD) (a : ℕ) (ha : a < 64) (h : D.depthFit = true) :
    maxDepthW (D.at a) < 2 ^ 64 := by
  unfold WholeD.depthFit at h
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true] at h
  have h1 : maxDepthT D.ds₁ ≤ 63 := Johnson.G.maxDepthT_le h.1
  have h2 : maxDepthT D.ds₂ ≤ 63 := Johnson.G.maxDepthT_le h.2.1
  have h3 : maxDepthT D.ds₃ ≤ 63 := Johnson.G.maxDepthT_le h.2.2
  have h4 : maxDepthW (D.at a) ≤ 63 :=
    max_le (Nat.le_of_lt_succ ha) (max_le h1 (max_le h2 h3))
  exact Nat.lt_of_le_of_lt h4 (by decide)

/-- The entry file's greatest depth. -/
theorem maxDepthL_lt (ds : List TypedOracleCompiler.Run.PQ.RD) (a : ℕ) (ha : a < 64)
    (h : ∀ d ∈ ds, ∀ s ∈ d.trees, s.a < 64) :
    max (TypedOracleCompiler.Run.PQ.maxDepth ds) a < 2 ^ 64 := by
  have h1 : TypedOracleCompiler.Run.PQ.maxDepth ds ≤ 63 :=
    Johnson.G.foldl_max_le (fun d : TypedOracleCompiler.Run.PQ.RD => TypedOracleCompiler.Run.PQ.depthOf d.trees) 63
      ds 0 (Nat.zero_le _)
      fun d hd => Johnson.G.foldl_max_le (fun s : Fmt.Shape => s.a) 63 d.trees 0 (Nat.zero_le _)
        fun s hs => Nat.le_of_lt_succ (h d hd s hs)
  exact Nat.lt_of_le_of_lt (max_le h1 (Nat.le_of_lt_succ ha)) (by decide)

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- **Caps, depths and widths.** -/
theorem publicOwes_of (capT capL capB : ℕ → ℕ)
    (hN : NumbersFit (KF S.DK S.DP) S.DK dsF S.DP)
    (wK : ∀ d ∈ S.DK.ds₁ ++ (S.DK.ds₂ ++ S.DK.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (wP : ∀ d ∈ S.DP.ds₁ ++ (S.DP.ds₂ ++ S.DP.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64)
    (hT : ∀ j, capT j < 2 ^ 64) (hL : ∀ j, capL j < 2 ^ 64) (hB : ∀ j, capB j < 2 ^ 64) :
    PublicOwes S capT capL capB where
  capT := hT
  capL := hL
  capB := hB
  depT := maxDepthW_lt S.DK frS.P.T.a publicL_full.depth hN.depthK
  depB := maxDepthW_lt S.DP frS.P.T.a publicL_full.depth hN.depthP
  depL := maxDepthL_lt dsF frS.P.T.a publicL_full.depth
    fun d hd s hs => (publicL_full.shapes d hd s hs).2.1
  widT := wK
  widB := wP

/-- `GoodOwes` at the written draw does not hang on the maker of the interactive provers' coins: it
reads the draw's six other fields alone. -/
theorem goodOwes_anyMk {Kap₀ Kap Kap' : Type} (mk : Kap₀ → Runs4 → Kap) (mk' : Kap₀ → Runs4 → Kap')
    (N : DrawNums) (c : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC S c₀ m₀)) (capT capL capB : ℕ → ℕ) (i : (R S c₀ m₀).Index)
    (r₁ : (R S c₀ m₀).protocol.EncodingRandomness) (s₁ : ℕ → Bits)
    (x : DrawRaw (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap₀)
    (h : GoodOwes S c₀ m₀ c salt sL bcT bcL bcB capT capL capB i r₁ s₁ (drawAt mk N c x)) :
    GoodOwes S c₀ m₀ c salt sL bcT bcL bcB capT capL capB i r₁ s₁ (drawAt mk' N c x) :=
  ⟨h.c32, h.formT, h.formL, h.formB, h.coT, h.coB, h.coL, h.depthL, h.capT, h.capL, h.capB, h.depT,
    h.depB, h.depL, h.widT, h.widB, h.number, h.tableK, h.tableC⟩

/-- Nor does `DrawFit`. -/
theorem drawFit_anyMk {Kap₀ Kap Kap' : Type} (mk : Kap₀ → Runs4 → Kap) (mk' : Kap₀ → Runs4 → Kap')
    (N : DrawNums) (c : ByteArray)
    (x : DrawRaw (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap₀)
    (h : DrawFit (R S c₀ m₀).queryLayout (R S c₀ m₀).compilerParameters (drawAt mk N c x)) :
    DrawFit (R S c₀ m₀).queryLayout (R S c₀ m₀).compilerParameters (drawAt mk' N c x) :=
  ⟨h.s, h.T, h.Lk, h.B⟩

variable (n : ℕ)

/-- the re-bound input -/
local notation "ℜ" => InnerCompilerInput.reBound (R S c₀ m₀) n

set_option maxRecDepth 20000 in
/-- **`GoodOwesB` at the written draw, at every raw value.** -/
theorem goodOwesB_drawK {Kap₀ Kap : Type} (κOf : Kap₀ × Runs4 → Kap) (c : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (capT capL capB : ℕ → ℕ) (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness)
    (o₁ : ℕ → ByteArray) (x : DrawRaw (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap₀)
    (hL : sL.logLeaves = 0) (hc : c.size = 32) (h64 : saltG S.G ≤ 64)
    (hP : PublicOwes S capT capL capB) (hE : HonestEnc S.E)
    (h₁ : ∀ j, j < 2 ^ frS.P.T.a → (o₁ j).size ≤ 64) :
    GoodOwesB S c₀ m₀ n c (saltG S.G) sL (x.bT.tidy (saltG S.G) (sTG S.G))
      (x.bL.tidy (saltG S.G) sL) (x.bB.tidy (saltG S.G) (sBG S.G)) capT capL capB i r₁
      (fun j => leafSalt c (o₁ j)) (drawK κOf (numsAt S sL) c x) :=
  goodOwes_anyMk S c₀ m₀ Prod.mk (fun k r => κOf (k, r)) (numsAt S sL) c (saltG S.G) sL _ _ _ capT
    capL capB i r₁ _ x
    (goodOwes_drawAt S c₀ m₀ Prod.mk Prod.snd (fun _ _ _ => rfl) c sL capT capL capB i r₁ o₁ x hL hc
      h64 hP hE h₁)

set_option maxRecDepth 20000 in
/-- **`DrawFit` there.** -/
theorem drawFitB_drawK {Kap₀ Kap : Type} (κOf : Kap₀ × Runs4 → Kap) (c : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (x : DrawRaw (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap₀)
    (hL : sL.logLeaves = 0) (hc : c.size = 32) (h64 : saltG S.G ≤ 64) :
    DrawFit (ℜ).queryLayout (ℜ).compilerParameters (drawK κOf (numsAt S sL) c x) :=
  drawFit_anyMk S c₀ m₀ Prod.mk (fun k r => κOf (k, r)) (numsAt S sL) c x
    (drawFit_of_draw S c₀ m₀ c sL Prod.snd _ _ _ _
      (drawOwes_drawAt Prod.mk Prod.snd (fun _ _ _ => rfl) (numsAt S sL) c x h64) hL hc)

end Johnson.Prover.Print

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Slice
open _root_.Run (leafSalt)
open LPFD.Full (sBG sTG saltG)
open OnBytes.Prover OnBytes.Prover.Print
open Johnson.Prover.Print

/- Lean compares these by their names (as in Johnson/Goal/Description/AtBound.lean). -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- the input there -/
local notation "ℌ" => Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []
/-- the letters of the public files -/
local notation "𝔖" => dataAtFiles flashProveData Z

set_option maxRecDepth 100000 in
/-- **`GoodOwesB` at the goals' description, at the written draw, at every raw value**: in scope,
under protocolDataWellFormed. -/
theorem good_home {Kap₀ Kap : Type} (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (κOf : Kap₀ × Runs4 → Kap) (c : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (capT capL capB : ℕ → ℕ) (i : (ℌ).Index) (r₁ : (ℌ).protocol.EncodingRandomness)
    (o₁ : ℕ → ByteArray) (x : DrawRaw (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap₀)
    (hL : sL.logLeaves = 0) (hc : c.size = 32)
    (hT : ∀ j, capT j < 2 ^ 64) (hLk : ∀ j, capL j < 2 ^ 64) (hB : ∀ j, capB j < 2 ^ 64)
    (h₁ : ∀ j, j < 2 ^ frS.P.T.a → (o₁ j).size ≤ 64) :
    GoodOwesB 𝔖 allZeroDigest [] (b Z) c (saltG (𝔖).G) sL (x.bT.tidy (saltG (𝔖).G) (sTG (𝔖).G))
      (x.bL.tidy (saltG (𝔖).G) sL) (x.bB.tidy (saltG (𝔖).G) (sBG (𝔖).G)) capT capL capB i r₁
      (fun j => leafSalt c (o₁ j)) (drawK κOf (numsAt 𝔖 sL) c x) :=
  goodOwesB_drawK 𝔖 allZeroDigest [] (b Z) κOf c sL capT capL capB i r₁ o₁ x hL hc
    (Meaning.sizesSay_the Z scope live).salt
    (publicOwes_of 𝔖 capT capL capB (Meaning.numbersFit_the Z)
      (Meaning.sizesSay_the Z scope live).widthsK (Meaning.sizesSay_the Z scope live).widthsP hT hLk
      hB)
    (Meaning.honestEnc_the Z) h₁

set_option maxRecDepth 100000 in
/-- **`DrawFit` there**, at every raw value. -/
theorem drawFit_drawK_home {Kap₀ Kap : Type} (κOf : Kap₀ × Runs4 → Kap) (c : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (x : DrawRaw (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap₀)
    (hL : sL.logLeaves = 0) (hc : c.size = 32) (h64 : saltG (𝔖).G ≤ 64) :
    DrawFit (ℌ).queryLayout (ℌ).compilerParameters (drawK κOf (numsAt 𝔖 sL) c x) :=
  drawFitB_drawK 𝔖 allZeroDigest [] (b Z) κOf c sL x hL hc h64

set_option maxRecDepth 100000 in
/-- **What the reading runs gives at the written draw's coins**: the four run values of the two tidy
byte coins. -/
theorem same_home {Kap₀ Kap : Type} (κOf : Kap₀ × Runs4 → Kap) (runs : Kap → Runs4)
    (hκ : ∀ k r, Runs4.Fit r → runs (κOf (k, r)) = r) (c : ByteArray)
    (sL : OnBytes.Params.LinBindingShape) (x : DrawRaw (ℌ).protocol (ℌ).LeafBody (ℌ).offlineRoundSplits (ℌ).linkRoundSplits Kap₀)
    (h64 : saltG (𝔖).G ≤ 64) :
    runs (drawK κOf (numsAt 𝔖 sL) c x).κ =
      (((x.bT.tidy (saltG (𝔖).G) (sTG (𝔖).G)).run2, (x.bT.tidy (saltG (𝔖).G) (sTG (𝔖).G)).run3),
        ((x.bB.tidy (saltG (𝔖).G) (sBG (𝔖).G)).run2,
          (x.bB.tidy (saltG (𝔖).G) (sBG (𝔖).G)).run3)) :=
  (drawOwes_drawK κOf runs hκ (numsAt 𝔖 sL) c x h64).same

set_option maxRecDepth 100000 in
/-- The told part of the public reading's value is the drawn digest. -/
theorem part_home (hash : VerifiableInference.Hash) :
    (LayoutsByPublicReading.reBound (HonestTerms.T (theTerms placeHolderCoins) Z) (b Z)).part
      (cAt Z hash, sevenAt Z hash) = cAt Z hash := by
  exact rfl

end FlashProve
