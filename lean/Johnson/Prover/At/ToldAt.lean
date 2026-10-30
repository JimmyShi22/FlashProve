-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/ToldAt.lean: the told record at the letters S of one set of public files
(`DescriptionDataAtFiles.layoutsByPublicReading`, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean), held against the input at the two public readings
(`innerCompilerInputAtFullSize (S.inputFieldsAtReadings c m)`): what its public reading returns at a hash function, and the
premises on wires, marks and caps at a reading d. Then the tests on public numbers at the
goals' description, at all public files.

Main names.
  `pub_det_layoutsByPublicReading` (namespace `FlashProve`)   the told record's public reading returns, at every hash
      function, the pair (cAt Z hash, sevenAt Z hash)
  `wiresFit_famD`, `lawFit_famD`, `num_famD` (namespace `VerifiableInference.OnPublicFiles`)   `WiresFit`,
      `LawFit` and the yes of the test of the copy's number at the told record of a family
      (`toldFamD`, Johnson/Flat/Told/FamilyD.lean), in that record's own letters; for all data
  `wiresFit_layoutsByPublicReading`, `lawFit_layoutsByPublicReading`, `num_layoutsByPublicReading`   their calls at S
  `numbersFit_the` (namespace `Meaning`)   `NumbersFit` at the description's letters
      `dataAtFiles flashProveData Z`, at all public files Z: no premise

Kin in the library, called here: `DescriptionDataAtFiles.at_layoutsByPublicReading` (the told record's input at d is the input at d);
`VerifierAndGoals.Told.reads_pub8` (Johnson/Flat/Told/Reads.lean; `reads_descriptionOfFields`,
Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFields.lean, is its call at a description); `parts_the`
(Johnson/Goal/Conditions/BindsAtThe.lean: what the yes of the frame's one test says, at every Z).

Limits. Equations and calls. At public files where the frame's test says no the description lays
data without a round: `numbersFit_the` holds there too and says little. Nothing says that a verifier
says yes. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.FitAt
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields
import Johnson.Goal.Conditions.BindsAtThe
import Johnson.Goal.Meaning.PublicFitAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open TypedOracleCompiler.Compile.Batch (OneProtocolProof PlainPart.depth)
open TypedOracleCompiler.Joined (pls₁)
open OnBytes.K.Arm.Pub (D8)
open OnBytes.Prover (WiresFit LawFit)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  {T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}
  (U : FamLettersD T₀) (d : D8)

/-! ## At the told record of a family, for all data -/

set_option maxRecDepth 20000 in
theorem wiresFit_famD (h : NumbersFit K DK ds DP) :
    WiresFit (innerCompilerInputAtFullSize T₀).queryLayout ((toldFamD U).cA d) :=
  wiresFit_fullD (lettersFamD U d) h

set_option maxRecDepth 20000 in
theorem lawFit_famD (h : NumbersFit K DK ds DP) (h0 : PlainPart.depth _ _ T₀.pl0 = 0)
    (h1 : PlainPart.depth _ _ T₀.pl1 = 0) (capT capL capB : ℕ → ℕ) :
    LawFit (innerCompilerInputAtFullSize T₀).queryLayout ((toldFamD U).Sd d) capT capL capB :=
  lawFit_fullD (lettersFamD U d) h h0 h1 capT capL capB

set_option maxRecDepth 20000 in
theorem num_famD (hn : T₀.num = PV.Front.numCopy) (copy : ℕ)
    (π : OneProtocolProof 256 (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
                  silP runP).batch)
    (h : (pls₁ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP) π).1.copy = copy) :
    ((toldFamD U).Sd d).num copy π.plains = true :=
  num_fullD (lettersFamD U d) hn copy π h

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof PlainPart.depth)
open TypedOracleCompiler.Joined (pls₁)
open OnBytes.K.Arm.Pub (D8)
open LPFD.Full (KF sBG)
open PV.EntryFive (dsF xsF)
open OnBytes.Prover (WiresFit LawFit)

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

/-- **What the told record's public reading returns at a hash function.** -/
theorem pub_det_layoutsByPublicReading (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (Z : PublicFiles) (c₀ : Digest)
    (m₀ : List (Dig 256)) (hash : VerifiableInference.Hash) :
    ((S Z).layoutsByPublicReading c₀ m₀).Pub.det (famOne hash) = (cAt Z hash, sevenAt Z hash) := by
  have h := Told.reads_pub8 Z hash
  rw [DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen] at h
  exact h.symm

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) (d : D8)

/-! ## The premises on wires, marks and caps -/

/-- the family's letters at S -/
local notation "𝔉" => LPFD.Full.famD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it
  Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)

set_option maxRecDepth 20000 in
theorem wiresFit_layoutsByPublicReading (h : NumbersFit (KF S.DK S.DP) S.DK dsF S.DP) :
    WiresFit (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout ((S.layoutsByPublicReading c₀ m₀).cA d) :=
  wiresFit_famD 𝔉 d h

set_option maxRecDepth 20000 in
theorem lawFit_layoutsByPublicReading (h : NumbersFit (KF S.DK S.DP) S.DK dsF S.DP) (capT capL capB : ℕ → ℕ) :
    LawFit (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout ((S.layoutsByPublicReading c₀ m₀).Sd d) capT capL capB :=
  lawFit_famD 𝔉 d h (depth_pl0_tOf S c₀ m₀) (depth_pl1_tOf S c₀ m₀) capT capL capB

set_option maxRecDepth 20000 in
theorem num_layoutsByPublicReading (copy : ℕ)
    (π : OneProtocolProof 256 (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
                  ByteArray.empty silP S.runP).batch)
    (h : (pls₁ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP) π).1.copy = copy) :
    ((S.layoutsByPublicReading c₀ m₀).Sd d).num copy π.plains = true :=
  num_famD 𝔉 d (num_tOf S c₀ m₀) copy π h

end FlashProve

namespace Meaning
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference.OnPublicFiles (NumbersFit)
open LPFD.Full (KF)
open PV.EntryFive (dsF)

/-- **The tests on public numbers hold at the description's letters, at all public files.** -/
theorem numbersFit_the (Z : PublicFiles) :
    NumbersFit (KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) (dataAtFiles flashProveData Z).DK dsF
      (dataAtFiles flashProveData Z).DP where
  blocks := (parts_the Z).hk
  entry := (parts_the Z).hE
  workK := (parts_the Z).wK
  depthK := (parts_the Z).dK
  workP := (parts_the Z).wP
  depthP := (parts_the Z).dP
  fewK := (madeFit_DK Z).few
  fewL := Johnson.Prover.Print.publicL_full.few
  fewP := (madeFit_DP Z).few

end Meaning
