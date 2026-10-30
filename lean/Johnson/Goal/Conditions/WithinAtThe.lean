-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/WithinAtThe.lean: **the verifier's own queries are within verifierQueryAllowance**
  (VerifierWithin, Ladder/Bits.lean:128: the first half of G7bits | G8bits), general in S, then at
  theBound K (Johnson/Goal/Conditions/BindsAtThe.lean): there without a premise.
  queryBound_readMoreAt     the further reading at any ground asks at most seven queries, at every
    digest c (queryBound_askListL, Johnson/Flat/Told/Reads.lean; par7_length,
    Johnson/Top/KeyTree.lean)
  **verifierWithin_star**   at descriptionOfFields (fun Z => (S Z).toDescriptionFields) H: from: at every Z in scope: the
    frame's one test on numbers says yes at S Z's letters and v · the parser asks at most qP · 2 + 7
    + qP + v ≤ verifierQueryAllowance
  **verifierWithin_theBound**   VerifierWithin (theBound K o), at every K and o: no premise: v :=
    theQueries = 2^20 (fit_theLay, NumbersAtThe.lean: at every Z) · qP := 1 (descriptionOfDataOnBytes_within,
    Johnson/Goal/Tie/DescriptionOfData.lean) · 2 + 7 + 1 + 2^20 ≤ 2^23
Who reads each letter. c m (under «for all» in VerifierWithin): the wiring's count hangs on neither
  (verifierQueryCountBound_descriptionDataAtFiles's right side names none). K: nobody (withTerms turns neither readMore, parse nor input).
  ∃: qMore qParse: laid as 7 and qP: numerals; nothing that the verifier reads is chosen.
Does not show. The other half of G8bits (SoundUnderPolicyAt … bits): that wants the named bound on a
  round's error at about 2.57 / 2^128 (Ladder/Bits.lean's own head) and is not touched here. Where
  protocolDataWellFormed says no the count is that of a verifier without rounds. The form: the count is
  of the rounds' data that sit in flashProveData's seats (Johnson/Goal/Description/KeyFold.lean,
  ProofFold.lean). tVC counts typed queries as the compiler counts them. Nothing on soundness.
No soundness is claimed.
-/
import Johnson.Goal.Conditions.ToldBound
import Johnson.Goal.Conditions.BindsAtThe
import Johnson.Flat.Told.Reads
import Johnson.Top.KeyTree
import Ladder.Bits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF GF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 theCoding theKeyData
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem


/-- The further reading asks at most seven queries, at every digest. -/
theorem queryBound_readMoreAt (G : EntryGround) (Z : PublicFiles) (c : Digest) :
    (readMoreAt G Z c).toRandomized.QueryBound 7 :=
  queryBound_mono_det _ _ _
    (by
      unfold ssOf
      rw [List.length_map]
      exact TypedOracleCompiler.Compile.Batch.Cms.par7_length G Z.pol Z.KL Z.lay _)
    (VerifierAndGoals.Told.queryBound_askListL (ssOf (par7 G Z.pol Z.KL Z.lay) c))

/-- **The verifier's own queries at D⋆, from the frame's test on numbers and the parser's count.** -/
theorem verifierWithin_star (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (v qP : ℕ)
    (fit : ∀ Z, InScope Z = true → sizeNumbersFitAtFullSize (KF (S Z).DK (S Z).DP) v (S Z).G.c.first.binding.logLeaves
      (S Z).G.k.oneTime.binding.logLeaves (S Z).DK (S Z).DP dsFull frD.xs = true)
    (hP : ∀ Z, InScope Z = true → Parser.Within ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).parse Z) qP)
    (hn : 2 + 7 + qP + v ≤ verifierQueryAllowance) : VerifierWithin (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) :=
  fun Z hZ => ⟨7, qP, fun c => queryBound_readMoreAt recordGround Z c, hP Z hZ, fun c m =>
    le_trans (Nat.add_le_add_left (verifierQueryCountBound_descriptionDataAtFiles (S Z) c m v (fit Z hZ)) _) hn⟩

variable (K : TheCoins)

/-- **At the closed description with the terms laid in: no premise.** -/
theorem verifierWithin_theBound (o : SecondHashFunctionType) : VerifierWithin (theBound K o) :=
  verifierWithin_star (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) theQueries 1
    (fun Z _ => fit_theLay Z) (fun Z _ => descriptionOfDataOnBytes_within flashProveData Z)
    (by unfold theQueries verifierQueryAllowance; norm_num)

end FlashProve

#print axioms FlashProve.queryBound_readMoreAt
#print axioms FlashProve.verifierWithin_star
#print axioms FlashProve.verifierWithin_theBound
