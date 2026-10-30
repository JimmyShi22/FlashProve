-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/Printed.lean: from what the prover of a whole request returns, two of the
interactive verifiers' yes and the compiled verifier's yes, to the yes of the goals' verify at the
form that is printed of it: at the letters S of the public files, in the letters of the told record
(`DescriptionDataAtFiles.layoutsByPublicReading`, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean) at the public reading under a hash function.

Main names (namespace `Johnson.Prover.Print`).
  `key_of_ends`, `vra_of_ends`, `plainsB_of_ends`   for all wirings: where `Ends`
      (Johnson/Prover/All/Good.lean) holds, the committer's key under g is the kept tree's root
      with the honest OOD sample at the first seed; so the compiled verifier's yes at that key and
      the proof is its yes at the written parts; the proof file's string has the plain parts of its
      transcript
  `yes_of_vra_parts`   `yes_of_vra_told` with the nine parts of the typed proof as letters
  `printed_star`   R the told record's ground input, T the told record, d₈ the pair
      (cAt Z hash, sevenAt Z hash), g the typed oracle functions that are read off the hash function
      through T.m d₈: PublicS · the tests on public numbers · `Ends` at R.queryLayout, T.Sd d₈, T.cA d₈, g ·
      the key file's and the proof file's interactive verifiers accept · `GoodOwes`
      (Johnson/Prover/Print/FitsOfGood.lean) at the drawn digest's bytes · what is asked of the two
      strategies (`StratOwes`, Johnson/Prover/Print/OwesOf.lean) · the test of the copy's number
      says yes at the proof file's transcript · the instance is built of (prompt, output) and no
      further token · `verifyAtKeyRoot` says yes at the committer's own key: then the proof is laid of three
      strings, and verify evaluates to true at the commitment
      `digestUnder hash T.encT (T.part d₈, key)` and at the form that is printed of the nine parts

By: `fits_of_good`, `yes_of_vra_told` (Johnson/Prover/At/YesTold.lean), `wiresFit_layoutsByPublicReading`
(Johnson/Prover/At/ToldAt.lean), `copy_of_num_layoutsByPublicReading` (Johnson/Prover/At/NumBack.lean), `det_committerAtFixedCoins`,
`det_seedsO` (Johnson/Prover/All/Yes.lean).

Limits. No probability. Each premise is asked, none is shown here (`GoodOwesB` at the goals'
description: good_home, Johnson/Prover/At/DrawHome.lean): above all `GoodOwes`, `StratOwes`, the
accepts, and that `verifyAtKeyRoot` says yes. The verifier is the goals' verify at the description `descriptionOnBytes S
f₀ Hb`; nothing is said of another argument system's. No goal is stated. Nothing on soundness or
completeness.

Local letters (notation of one section). 𝔗: the told record at Z, DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀ · ℜ: its
  ground input, R (S Z) c₀ m₀ · 𝔡: the public reading under the hash function, (cAt Z hash, sevenAt
  Z hash) · 𝔤: the typed oracle functions that are read off the hash function there.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FitsOfGood
import Johnson.Prover.At.YesTold
import Johnson.Prover.At.NumBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Compile (Params)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined (pls₁)
open LPFD.Full (XF sBG sTG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print

section
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
  (Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (b₀ : Bd)
  (st : Strats L Kap) (capT capL capB : ℕ → ℕ) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
  (i : I) (r₁ : L.EncodingRandomness) (s₁ : ℕ → Bits) (x : X) (d : Draw lam L Bd aT aL Kap)
  (π : OfflineLinkOnlineProof lam L aT aL) (e₁ e₂ : L.OutOfDomainSeed) (τT : Tr L.offline.shape) (τL : Tr L.link.shape)
  (τB : Tr L.onlineBatch.loc.shape)

/-- Where `Ends` holds, the committer's key is the kept tree's root with the honest OOD sample at
the first seed. -/
theorem key_of_ends (hE : Ends W Sd cA r₀ b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB) :
    ((committerAtFixedCoins W Sd b₀ i r₁ s₁).det g).1 =
      ⟨((committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g).root, L.recOf i r₁ e₁⟩ := by
  rw [det_committerAtFixedCoins, det_seedsO, ← hE.seed₁]

/-- So the compiled verifier's yes at that key and the proof is its yes at the written parts. -/
theorem vra_of_ends (hE : Ends W Sd cA r₀ b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB)
    (π' : OfflineLinkOnlineProof lam L aT aL) (hπ : π = π')
    (hv : (verifyAtKeyRoot W Sd cA r₀ p ((committerAtFixedCoins W Sd b₀ i r₁ s₁).det g).1 x π).det g = true) :
    (verifyAtKeyRoot W Sd cA r₀ p ⟨((committerTreeKeptByProver W b₀ (L.encodeIndex i r₁) s₁).det g).root, L.recOf i r₁ e₁⟩ x π').det g =
      true := by
  rw [key_of_ends W Sd cA r₀ b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB hE, hπ] at hv
  exact hv

/-- The proof file's string has the plain parts of its transcript. -/
theorem plainsB_of_ends (hE : Ends W Sd cA r₀ b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB)
    (n : ℕ) (πT : Option (OneProtocolProof lam (batTC L aT)))
    (lk : Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL))) (πB : OneProtocolProof lam L.onlineBatch)
    (hπ : π = ⟨n, πT, lk, some πB⟩) : πB.plains = τB.plains := by
  obtain ⟨πT₀, πL₀, πB₀, hπ₀, -, -, -, -, -, pB⟩ := hE.fields
  have e := hπ₀.symm.trans hπ
  injection e with _ _ _ e3
  injection e3 with e3
  rw [← e3]
  exact pB

end

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)
  (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles) (hash : VerifiableInference.Hash)

/-- the told record at Z -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀
/-- its ground input -/
local notation "ℜ" => R (S Z) c₀ m₀
/-- the public reading under the hash function -/
local notation "𝔡" => (cAt Z hash, sevenAt Z hash)
/-- the typed oracle functions that are read off the hash function there -/
local notation "𝔤" =>
  readBlocks (LayoutsByPublicReading.m (DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀) (cAt Z hash, sevenAt Z hash)) (famOne hash)

set_option maxRecDepth 20000 in
/-- `yes_of_vra_told` with the nine parts as letters: so that a call at written parts compares no
field of a written record. -/
theorem yes_of_vra_parts (scope : VerifierAndGoals.InScope Z = true) (prompt output : List Token)
    (aux : List Token) (cm : Dig 256) (rcd : RecFull) (copy : ℕ) (piT : OneProtocolProof 256 (QT (S Z)))
    (cm' : Dig 256) (rcd' : RecFull) (piL : OneProtocolProof 256 (QL (S Z))) (piB : OneProtocolProof 256 (QB (S Z)))
    (hS : PublicS (S Z))
    (hq : Fits (S Z) (digToBytes (cAt Z hash)) ⟨aux, cm, rcd, copy, piT, cm', rcd', piL, piB⟩)
    (x : (ℜ).Instance) (hb : (ℜ).buildInstance (prompt, output) aux = some x)
    (hv : (verifyAtKeyRoot (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample (ℜ).compilerParameters ⟨cm, rcd⟩ x
      ⟨copy, some piT, (cm', rcd', some piL), some piB⟩).det 𝔤 = true) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z)
      (ZKCP.digestUnder hash (𝔗).encT ((𝔗).part 𝔡, ⟨cm, rcd⟩)) prompt output
      (formOf (S Z) ⟨aux, cm, rcd, copy, piT, cm', rcd', piL, piB⟩)).evaluate hash = true :=
  yes_of_vra_told S f₀ Hb c₀ m₀ Z scope hash prompt output
    ⟨aux, cm, rcd, copy, piT, cm', rcd', piL, piB⟩ hS hq x hb hv

set_option maxRecDepth 20000 in
/-- **From what the prover of a whole request returns to verify's yes at the printed form.** -/
theorem printed_star {Kap : Type} (scope : VerifierAndGoals.InScope Z = true) (prompt output : List Token)
    (b₀ : (ℜ).LeafBody) (st : Strats (ℜ).protocol Kap) (capT capL capB : ℕ → ℕ)
    (i : (ℜ).Index) (r₁ : (ℜ).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : XF)
    (d : Draw 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits Kap) (π : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (e₁ e₂ : (ℜ).protocol.OutOfDomainSeed) (τT : Tr (QT (S Z)).loc.shape) (τL : Tr (QL (S Z)).loc.shape)
    (τB : Tr (QB (S Z)).loc.shape) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC (S Z) c₀ m₀)) (hS : PublicS (S Z))
    (hN : NumbersFit (KF (S Z).DK (S Z).DP) (S Z).DK dsF (S Z).DP)
    (hE : Ends (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL capB 𝔤 i r₁ s₁ x d π e₁ e₂ τT τL
      τB)
    (aT : (QT (S Z)).loc.accept ((ℜ).protocol.recOf i r₁ e₁) ((ℜ).protocol.encodeIndex i r₁) τT = true)
    (aB : (QB (S Z)).loc.accept (x, (ℜ).protocol.recOf i d.r e₂) ((ℜ).protocol.encodeIndex i d.r) τB = true)
    (hG : GoodOwes (S Z) c₀ m₀ (digToBytes (cAt Z hash)) salt sL bcT bcL bcB capT capL capB i r₁ s₁
      d)
    (hσ : ∀ (πT : OneProtocolProof 256 (QT (S Z))) (πL : OneProtocolProof 256 (QL (S Z))) (πB : OneProtocolProof 256 (QB (S Z))),
      π = ⟨d.n, some πT, (((committerTreeKeptByProver (ℜ).queryLayout b₀ ((ℜ).protocol.encodeIndex i d.r) d.s).det 𝔤).root,
          (ℜ).protocol.recOf i d.r e₂, some πL), some πB⟩ →
      StratOwes (ckP .two) ((S Z).DK.at frS.P.T.a) (front₀ (S Z).G.rec₀) (join₀ (S Z).G.rec₀)
          ByteArray.empty silK (S Z).runK bcT πT ∧
        StratOwes (ckP .two) ((S Z).DP.at frS.P.T.a) (front₀ (S Z).G.z₀.2) (join₀ (S Z).G.z₀.2)
          ByteArray.empty silP (S Z).runP bcB πB)
    (hn : ((𝔗).Sd 𝔡).num d.n τB.plains = true)
    (hb : (ℜ).buildInstance (prompt, output) [] = some x)
    (hv : (verifyAtKeyRoot (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample (ℜ).compilerParameters
      ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd 𝔡) b₀ i r₁ s₁).det 𝔤).1 x π).det 𝔤 = true) :
    ∃ (πT : OneProtocolProof 256 (QT (S Z))) (πL : OneProtocolProof 256 (QL (S Z))) (πB : OneProtocolProof 256 (QB (S Z))),
      π = ⟨d.n, some πT, (((committerTreeKeptByProver (ℜ).queryLayout b₀ ((ℜ).protocol.encodeIndex i d.r) d.s).det 𝔤).root,
          (ℜ).protocol.recOf i d.r e₂, some πL), some πB⟩ ∧
      (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z)
        (ZKCP.digestUnder hash (𝔗).encT
          ((𝔗).part 𝔡, ((committerAtFixedCoins (ℜ).queryLayout ((𝔗).Sd 𝔡) b₀ i r₁ s₁).det 𝔤).1))
        prompt output
        (formOf (S Z) ⟨[], ((committerTreeKeptByProver (ℜ).queryLayout b₀ ((ℜ).protocol.encodeIndex i r₁) s₁).det 𝔤).root,
          (ℜ).protocol.recOf i r₁ e₁, d.n, πT, ((committerTreeKeptByProver (ℜ).queryLayout b₀ ((ℜ).protocol.encodeIndex i d.r) d.s).det 𝔤).root,
          (ℜ).protocol.recOf i d.r e₂, πL, πB⟩)).evaluate hash = true := by
  obtain ⟨πT, πL, πB, hπ, hF⟩ := fits_of_good (S Z) c₀ m₀ ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) b₀ st capT capL
    capB 𝔤 i r₁ s₁ x d π e₁ e₂ τT τL τB (digToBytes (cAt Z hash)) salt sL bcT bcL bcB hE
    (wiresFit_layoutsByPublicReading (S Z) c₀ m₀ 𝔡 hN) aT aB hG fun πT πL πB hπ =>
      ⟨(hσ πT πL πB hπ).1, (hσ πT πL πB hπ).2, copy_of_num_layoutsByPublicReading (S Z) c₀ m₀ 𝔡 d.n πB (by
                          rw [plainsB_of_ends (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL capB 𝔤 i r₁ s₁ x d π
                            e₁ e₂ τT τL τB hE _ _ _ πB hπ]
                          exact hn)⟩
  refine ⟨πT, πL, πB, hπ, ?_⟩
  have hv' := vra_of_ends (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample (ℜ).compilerParameters b₀ st capT capL capB 𝔤 i r₁ s₁
    x d π e₁ e₂ τT τL τB hE _ hπ hv
  have hk := key_of_ends (ℜ).queryLayout ((𝔗).Sd 𝔡) ((𝔗).cA 𝔡) (ℜ).fixedSample b₀ st capT capL capB 𝔤 i r₁ s₁ x d π
    e₁ e₂ τT τL τB hE
  have main := yes_of_vra_parts S f₀ Hb c₀ m₀ Z hash scope prompt output _ _ _ _ _ _ _ _ _ hS hF x
    hb hv'
  rw [hk]
  exact main

end Johnson.Prover.Print
