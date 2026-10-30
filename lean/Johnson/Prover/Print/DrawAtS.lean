-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/DrawAtS.lean: AT THE LETTERS S OF ONE SET OF PUBLIC FILES: THE RECORD ON THE
DRAW (DrawOwes, Johnson/Prover/Print/DrawOwes.lean) AT THE PLAN's NUMBERS, WITH PUBLIC NUMBERS AND A
CODING OF THE FORMAT's CODE WORDS, GIVES GoodOwes (Johnson/Prover/Print/FitsOfGood.lean) AND DrawFit
(Johnson/Prover/All/Yes.lean).

Main names.
  numsAt S sL   the plan's numbers: saltG S.G · sTG S.G · sL · sBG S.G · the numbers of the joining
    round and of the seam of the two whole files · the copy's file's rounds and one.
  PublicOwes S capT capL capB   what is left of GoodOwes that is neither the draw's nor a table's:
    caps, depths and widths below 2^64.
  goodOwes_of_draw   DrawOwes at numsAt S sL · sL of depth 0 · c of 32 bytes · saltG S.G ≤ 64 ·
    PublicOwes · the coding's encoder gives tables of the format's code words (HonestEnc,
    Johnson/Prover/At/OwedAt.lean) · the key's leaves' salts are leafSalt c of at most 64 bytes:
    THEN GoodOwes.
  drawFit_of_draw    under the same: DrawFit.
  goodOwes_drawAt    so at the written draw drawAt mk (numsAt S sL) c x, at every raw value x.

By: tableOwes_fullD (Johnson/Prover/At/OwedAt.lean) · drawFit_of_good
(Johnson/Prover/Print/DrawOfGood.lean) · drawOwes_drawAt.

Its premises are not shown here. Where they stand at the goals' description: HonestEnc:
Meaning.honestEnc_the (Johnson/Prover/At/OwedAt.lean) · saltG S.G ≤ 64 and the widths: in scope,
under protocolDataWellFormed: Meaning.sizesSay_the (Johnson/Goal/Meaning/WordsFitAtThe.lean) · the three depths in
the form asked here: publicOwes_of (Johnson/Prover/At/DrawHome.lean), under NumbersFit (at the
description: numbersFit_the, Johnson/Prover/At/ToldAt.lean) and the widths · the caps (letters of
the prover) ARE PREMISES HERE; at the values capT, capL, capB of
Johnson/Goal/Conditions/HonestNumber.lean: capL_lt without a premise, capT_lt under S.DK =
writtenKFull, capB_lt under S.DP = writtenPFull (Johnson/Goal/Conditions/NumberAtHome.lean). Nothing
on how any program draws the raw value, and nothing is said of its distribution. Nothing on
soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.DrawOfGood
import Johnson.Prover.Print.DrawOwes

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- The plan's numbers. -/
noncomputable def numsAt (sL : OnBytes.Params.LinBindingShape) : DrawNums :=
  ⟨saltG S.G, sTG S.G, sL, sBG S.G, (GT S).nJ, (GT S).n3, dsF.length + 1, (GB S).nJ, (GB S).n3⟩

/-- Caps, depths and widths. -/
structure PublicOwes (capT capL capB : ℕ → ℕ) : Prop where
  capT : ∀ j, capT j < 2 ^ 64
  capL : ∀ j, capL j < 2 ^ 64
  capB : ∀ j, capB j < 2 ^ 64
  depT : maxDepthW (S.DK.at frS.P.T.a) < 2 ^ 64
  depB : maxDepthW (S.DP.at frS.P.T.a) < 2 ^ 64
  depL : (wL S (KF S.DK S.DP)).maxDepth < 2 ^ 64
  widT : ∀ e ∈ (S.DK.at frS.P.T.a).ds₁ ++ ((S.DK.at frS.P.T.a).ds₂ ++ (S.DK.at frS.P.T.a).ds₃),
    ∀ u ∈ e.trees, u.W < 2 ^ 64
  widB : ∀ e ∈ (S.DP.at frS.P.T.a).ds₁ ++ ((S.DP.at frS.P.T.a).ds₂ ++ (S.DP.at frS.P.T.a).ds₃),
    ∀ u ∈ e.trees, u.W < 2 ^ 64

/-- **FROM THE RECORD ON THE DRAW TO GoodOwes.** -/
theorem goodOwes_of_draw {Kap : Type} (c : ByteArray) (sL : OnBytes.Params.LinBindingShape)
    (runs : Kap → Runs4) (bcT bcL bcB : ByteCoins (LC S c₀ m₀)) (capT capL capB : ℕ → ℕ)
    (i : (R S c₀ m₀).Index) (r₁ : (R S c₀ m₀).protocol.EncodingRandomness) (o₁ : ℕ → ByteArray)
    (d : Draw 256 (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap)
    (hD : DrawOwes (numsAt S sL) c runs bcT bcL bcB d) (hL : sL.logLeaves = 0)
    (hc : c.size = 32) (h64 : saltG S.G ≤ 64) (hP : PublicOwes S capT capL capB)
    (hE : HonestEnc S.E) (h₁ : ∀ j, j < 2 ^ frS.P.T.a → (o₁ j).size ≤ 64) :
    GoodOwes S c₀ m₀ c (saltG S.G) sL bcT bcL bcB capT capL capB i r₁
      (fun j => leafSalt c (o₁ j)) d := by
  choose o ho he using hD.salts
  have es : d.s = fun j => leafSalt c (o j) := funext he
  exact
    { c32 := hc
      formT := hD.formT
      formL := hD.formL
      formB := hD.formB
      coT := hD.coT
      coB := hD.coB
      coL := hD.coL
      depthL := hL
      capT := hP.capT
      capL := hP.capL
      capB := hP.capB
      depT := hP.depT
      depB := hP.depB
      depL := hP.depL
      widT := hP.widT
      widB := hP.widB
      number := hD.number
      tableK := tableOwes_fullD (S.inputFieldsAtReadings c₀ m₀) hE i r₁ c o₁ hc h₁ _
      tableC := by
        rw [es]
        exact tableOwes_fullD (S.inputFieldsAtReadings c₀ m₀) hE i d.r c o hc
          (fun j _ => by rw [ho j]; exact h64) _ }

/-- **And to DrawFit.** -/
theorem drawFit_of_draw {Kap : Type} (c : ByteArray) (sL : OnBytes.Params.LinBindingShape)
    (runs : Kap → Runs4) (bcT bcL bcB : ByteCoins (LC S c₀ m₀))
    (d : Draw 256 (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap)
    (hD : DrawOwes (numsAt S sL) c runs bcT bcL bcB d) (hL : sL.logLeaves = 0)
    (hc : c.size = 32) : DrawFit (R S c₀ m₀).queryLayout (R S c₀ m₀).compilerParameters d :=
  drawFit_tOf S c₀ m₀ d sL bcT bcL bcB _ _ _ _ _ _ hL (fun j _ => hD.length_salts hc j) hD.formT
    hD.coT.fit hD.formL hD.coL hD.formB hD.coB.fit

/-- **At the written draw, at every raw value.** -/
theorem goodOwes_drawAt {Kap₀ Kap : Type} (mk : Kap₀ → Runs4 → Kap) (runs : Kap → Runs4)
    (hmk : ∀ k r, Runs4.Fit r → runs (mk k r) = r) (c : ByteArray)
    (sL : OnBytes.Params.LinBindingShape)
    (capT capL capB : ℕ → ℕ) (i : (R S c₀ m₀).Index) (r₁ : (R S c₀ m₀).protocol.EncodingRandomness) (o₁ : ℕ → ByteArray)
    (x : DrawRaw (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap₀)
    (hL : sL.logLeaves = 0) (hc : c.size = 32) (h64 : saltG S.G ≤ 64)
    (hP : PublicOwes S capT capL capB) (hE : HonestEnc S.E)
    (h₁ : ∀ j, j < 2 ^ frS.P.T.a → (o₁ j).size ≤ 64) :
    GoodOwes S c₀ m₀ c (saltG S.G) sL (x.bT.tidy (saltG S.G) (sTG S.G))
      (x.bL.tidy (saltG S.G) sL) (x.bB.tidy (saltG S.G) (sBG S.G)) capT capL capB i r₁
      (fun j => leafSalt c (o₁ j)) (drawAt mk (numsAt S sL) c x) :=
  goodOwes_of_draw S c₀ m₀ c sL runs _ _ _ capT capL capB i r₁ o₁ _
    (drawOwes_drawAt mk runs hmk (numsAt S sL) c x h64) hL hc h64 hP hE h₁

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.numsAt
#print axioms Johnson.Prover.Print.PublicOwes
#print axioms Johnson.Prover.Print.goodOwes_of_draw
#print axioms Johnson.Prover.Print.drawFit_of_draw
#print axioms Johnson.Prover.Print.goodOwes_drawAt
