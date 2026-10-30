-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/FitsOfEnds.lean: FROM WHAT THE PROVER OF A WHOLE REQUEST RETURNS (Ends,
Johnson/Prover/All/Good.lean) TO Fits (Johnson/Prover/Print/FormBack.lean) AT THE NINE PARTS OF ITS
KEY AND PROOF, at the input of the full size at the letters S of one set of public files.

Main names.
  R S c₀ m₀, LC S c₀ m₀   the input innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀); its carrier.
  fits_of_ends   Ends at R's wire record, at any seeds' record, answers' list, strategies, caps and
    oracle functions; the three coins are of the bytes' form; RunsOwe
    (Johnson/Prover/Print/FitsOfRuns.lean) at the proof's own three strings: THEN the proof is laid
    of three strings πT, πL, πB, and Fits S c holds of: no further token · the root of the kept tree
    over the key's table · the key's OOD sample · the draw's number · πT · the root of the kept tree
    over the copy's table · the copy's OOD sample · πL · πB.

By: Ends' three equations (the compiled prover's own) · proveTA_fullD, proveLA_fullD, proveBA_fullD
(Johnson/Prover/At/WiresAt.lean) · fits_of_runs.

Not shown here: that RunsOwe is met, nor that the coins are of the bytes' form. Nothing on
acceptance, soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FitsOfRuns
import Johnson.Prover.All.Good
import Johnson.Prover.At.WiresAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve Rom
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Compile (Tag)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open LPFD.Full (XF sBG sTG KF)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover OnBytes.Prover.Print

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- the input innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀) -/
noncomputable abbrev R := innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)
/-- the type typedOracleCarrier at R's protocol, LeafBody, offlineRoundSplits and linkRoundSplits -/
noncomputable abbrev LC := typedOracleCarrier (R S c₀ m₀).protocol (R S c₀ m₀).LeafBody (R S c₀ m₀).offlineRoundSplits (R S c₀ m₀).linkRoundSplits

/-- **FROM Ends TO Fits.** -/
theorem fits_of_ends {Kap : Type}
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
    (hT : d.coT = coinsOf (GT S).nJ (GT S).n3 (sTG S.G).logLeaves bcT)
    (hL : d.coL = coinsOf (dsF.length + 1) (dsF.length + 1) sL.logLeaves bcL)
    (hB : d.coB = coinsOf (GB S).nJ (GB S).n3 (sBG S.G).logLeaves bcB)
    (hO : ∀ (πT : OneProtocolProof 256 (QT S)) (πL : OneProtocolProof 256 (QL S)) (πB : OneProtocolProof 256 (QB S)),
      π = ⟨d.n, some πT,
        (((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
          (R S c₀ m₀).protocol.recOf i d.r e₂, some πL), some πB⟩ →
      RunsOwe S (L := LC S c₀ m₀) (K := KF S.DK S.DP) c salt sL bcT bcL bcB capT capL capB x
        ((R S c₀ m₀).protocol.encodeIndex i r₁) ((R S c₀ m₀).protocol.encodeIndex i r₁, (R S c₀ m₀).protocol.encodeIndex i d.r)
        ((R S c₀ m₀).protocol.encodeIndex i d.r)
        (fun _ => (committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁).det g)
        (fun k => if k = 0 then (committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁).det g
          else (committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g)
        (fun _ => (committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g)
        ⟨[], ((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁).det g).root,
          (R S c₀ m₀).protocol.recOf i r₁ e₁, d.n, πT,
          ((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
          (R S c₀ m₀).protocol.recOf i d.r e₂, πL, πB⟩ τT τL τB) :
    ∃ (πT : OneProtocolProof 256 (QT S)) (πL : OneProtocolProof 256 (QL S)) (πB : OneProtocolProof 256 (QB S)),
      π = ⟨d.n, some πT,
        (((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
          (R S c₀ m₀).protocol.recOf i d.r e₂, some πL), some πB⟩ ∧
      Fits S c ⟨[], ((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i r₁) s₁).det g).root,
        (R S c₀ m₀).protocol.recOf i r₁ e₁, d.n, πT,
        ((committerTreeKeptByProver (R S c₀ m₀).queryLayout b₀ ((R S c₀ m₀).protocol.encodeIndex i d.r) d.s).det g).root,
        (R S c₀ m₀).protocol.recOf i d.r e₂, πL, πB⟩ := by
  obtain ⟨πT, πL, πB, hπ, rT, rL, rB, -, -, -⟩ := hE.fields
  rw [hT, proveTA_fullD] at rT
  rw [hL, proveLA_fullD] at rL
  rw [hB, proveBA_fullD] at rB
  exact ⟨πT, πL, πB, hπ, fits_of_runs S (LC S c₀ m₀) (KF S.DK S.DP) c salt sL bcT bcL bcB capT capL
    capB x _ _ _ _ _ _ _ τT τL τB g Tag.test Tag.link Tag.onl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rT rL rB
    (hO πT πL πB hπ)⟩

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.fits_of_ends
