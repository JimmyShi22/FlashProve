-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/FitsOfGood.lean: fits_of_ends (Johnson/Prover/Print/FitsOfEnds.lean) WITH ITS
RECORD RunsOwe PAID AS FAR AS IT CAN BE: from what the prover of a whole request returns, two
accepts, the wires' laws, and named premises on the strategies, the draw, the two tables and some
numbers, TO Fits at the nine parts of its key and proof.

Main names.
  GoodOwes     THE NAMED PREMISES THAT ARE LEFT, in one record: the digest has 32 bytes · the three
    coins are of the bytes' form, with CoinsPrint (twice) and the entry's lengths at depth 0 · caps,
    depths, widths and the draw's number below 2^64 · TableOwes at the key's table with its salts
    and at the copy's.
  fits_of_good THE END. Beside GoodOwes it asks: Ends (Johnson/Prover/All/Good.lean) · WiresFit
    (Johnson/Prover/All/Yes.lean) · the key file's and the proof file's accept · of the proof's own
    strings: StratOwes twice, and that the proof file's front bears the draw's number.

By: fits_of_ends · owes_key, owes_proof, owes_entry (Johnson/Prover/Print/OwesOf.lean).

Not shown here: that a premise is met. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FitsOfEnds
import Johnson.Prover.Print.OwesOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined (pls₁ pls₂ pls₃)
open LPFD.Full (XF sBG sTG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- **The named premises that are left of RunsOwe (FitsOfRuns.lean).** -/
structure GoodOwes {Kap : Type} (c : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC S c₀ m₀)) (capT capL capB : ℕ → ℕ)
    (i : (R S c₀ m₀).Index) (r₁ : (R S c₀ m₀).protocol.EncodingRandomness) (s₁ : ℕ → Bits)
    (d : Draw 256 (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap) : Prop where
  c32 : c.size = 32
  formT : d.coT = coinsOf (GT S).nJ (GT S).n3 (sTG S.G).logLeaves bcT
  formL : d.coL = coinsOf (dsF.length + 1) (dsF.length + 1) sL.logLeaves bcL
  formB : d.coB = coinsOf (GB S).nJ (GB S).n3 (sBG S.G).logLeaves bcB
  coT : CoinsPrint bcT salt (sTG S.G)
  coB : CoinsPrint bcB salt (sBG S.G)
  coL : bcL.Fit salt sL
  depthL : sL.logLeaves = 0
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
  number : d.n < 2 ^ 64
  tableK : TableOwes (n := 2 ^ frS.P.T.a) c ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁ fun _ => True
  tableC : TableOwes (n := 2 ^ frS.P.T.a) c ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s fun _ => True

/-- **FROM THE GOOD CASE TO Fits.** -/
theorem fits_of_good {Kap : Type}
    (Sd : OutOfDomainSampleQueryLayout 256 (R S c₀ m₀).queryLayout.K (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits)
    (cA : (R S c₀ m₀).protocol.OutOfDomainAnswer → List (Dig 256)) (b₀ : (R S c₀ m₀).LeafBody)
    (st : Strats (R S c₀ m₀).protocol Kap) (capT capL capB : ℕ → ℕ)
    (g : Fam (typedOracleFamily 256 (R S c₀ m₀).queryLayout.K (LC S c₀ m₀)))
    (i : (R S c₀ m₀).Index) (r₁ : (R S c₀ m₀).protocol.EncodingRandomness) (s₁ : ℕ → Bits) (x : XF)
    (d : Draw 256 (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits Kap)
    (π : OfflineLinkOnlineProof 256 (R S c₀ m₀).protocol (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits)
    (e₁ e₂ : (R S c₀ m₀).protocol.OutOfDomainSeed) (τT : Tr (QT S).loc.shape) (τL : Tr (QL S).loc.shape)
    (τB : Tr (QB S).loc.shape)
    (c : ByteArray) (salt : ℕ) (sL : OnBytes.Params.LinBindingShape)
    (bcT bcL bcB : ByteCoins (LC S c₀ m₀))
    (hE : Ends (R S c₀ m₀).queryLayout Sd cA (R S c₀ m₀).fixedSample b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL
      τB)
    (hW : WiresFit (R S c₀ m₀).queryLayout cA)
    (aT : (QT S).loc.accept ((R S c₀ m₀).protocol.recOf i r₁ e₁) ((R S c₀ m₀).protocol.encodeIndex i r₁) τT = true)
    (aB : (QB S).loc.accept (x, (R S c₀ m₀).protocol.recOf i d.r e₂) ((R S c₀ m₀).protocol.encodeIndex i d.r) τB = true)
    (hG : GoodOwes S c₀ m₀ c salt sL bcT bcL bcB capT capL capB i r₁ s₁ d)
    (hσ : ∀ (πT : OneProtocolProof 256 (QT S)) (πL : OneProtocolProof 256 (QL S)) (πB : OneProtocolProof 256 (QB S)),
      π = ⟨d.n, some πT,
        (((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
          (R S c₀ m₀).protocol.recOf i d.r e₂, some πL), some πB⟩ →
      StratOwes (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty
          silK S.runK bcT πT ∧
        StratOwes (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty
          silP S.runP bcB πB ∧
        (pls₁ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
          ByteArray.empty silP S.runP) πB).1.copy = d.n) :
    ∃ (πT : OneProtocolProof 256 (QT S)) (πL : OneProtocolProof 256 (QL S)) (πB : OneProtocolProof 256 (QB S)),
      π = ⟨d.n, some πT,
        (((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
          (R S c₀ m₀).protocol.recOf i d.r e₂, some πL), some πB⟩ ∧
      Fits S c ⟨[], ((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁).det g).root,
        (R S c₀ m₀).protocol.recOf i r₁ e₁, d.n, πT,
        ((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
        (R S c₀ m₀).protocol.recOf i d.r e₂, πL, πB⟩ := by
  have hv : 2 ^ frS.P.v * 1 < 2 ^ 64 := by
    rw [frS_v]
    decide
  have ha : frS.P.T.a < 2 ^ 64 := Nat.lt_of_lt_of_le publicL_full.depth (by decide)
  obtain ⟨πT₀, πL₀, πB₀, hπ₀, -, -, -, pT, -, pB⟩ := hE.fields
  refine fits_of_ends S c₀ m₀ Sd cA b₀ st capT capL capB g i r₁ s₁ x d π e₁ e₂ τT τL τB c salt sL
    bcT bcL bcB hE hG.formT hG.formL hG.formB fun πT πL πB hπ => ?_
  obtain ⟨rfl, rfl, rfl⟩ : πT₀ = πT ∧ πL₀ = πL ∧ πB₀ = πB := by
    have e := hπ₀.symm.trans hπ
    injection e with _ e1 e2 e3
    injection e1 with e1
    injection e3 with e3
    injection e2 with _ e2
    injection e2 with _ e2
    injection e2 with e2
    exact ⟨e1, e2, e3⟩
  obtain ⟨sT, sB, hcB⟩ := hσ πT₀ πL₀ πB₀ hπ
  obtain ⟨oT, hans, hcT⟩ := owes_key (ckP .two) (S.DK.at frS.P.T.a) (front₀ S.G.rec₀)
    (join₀ S.G.rec₀) ByteArray.empty (R S c₀ m₀).queryLayout.K g
    (committerLeafInput (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁) s₁ c bcT ((R S c₀ m₀).protocol.encodeIndex i r₁) S.runK
    ((R S c₀ m₀).protocol.recOf i r₁ e₁) πT₀ τT sT pT aT hv (fun _ => rfl) ha hG.tableK
  have oB := owes_proof (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
    ByteArray.empty (R S c₀ m₀).queryLayout.K g (committerLeafInput (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s) d.s c
    bcB ((R S c₀ m₀).protocol.encodeIndex i d.r) S.runP (x, (R S c₀ m₀).protocol.recOf i d.r e₂) πB₀ τB sB pB aB
    (by rw [hcB]; exact hG.number) hv (fun _ => rfl) ha hG.tableC
  have oL := owes_entry (ckP .two) dsF frS.P.T.a xsF S.dec (R S c₀ m₀).queryLayout.K g
    ((R S c₀ m₀).protocol.recOf i r₁ e₁, (R S c₀ m₀).protocol.recOf i d.r e₂) ((R S c₀ m₀).protocol.encodeIndex i r₁)
    ((R S c₀ m₀).protocol.encodeIndex i d.r) (committerLeafInput (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁)
    (committerLeafInput (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s) s₁ d.s c τL (fun _ => rfl)
    (fun _ => rfl) ha hG.tableK hG.tableC
  exact
    { c32 := hG.c32, coT := hG.coT, coB := hG.coB, coL := hG.coL, depthL := hG.depthL
      fewJT := hW.fewT.1, few0T := hW.fewT.2, okT := hW.oka.T
      fewJB := hW.fewB.1, few0B := hW.fewB.2, okB := hW.oka.B, okL := hW.oka.Lk
      capT := hG.capT, capL := hG.capL, capB := hG.capB
      depT := hG.depT, depB := hG.depB, depL := hG.depL, widT := hG.widT, widB := hG.widB
      oweT := oT, oweB := oB, oweL := oL, ansT := hans, copyT := hcT, copyB := hcB }

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.GoodOwes
#print axioms Johnson.Prover.Print.fits_of_good
