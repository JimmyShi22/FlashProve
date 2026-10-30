-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/NumBack.lean: the converse of `num_fullD`, `num_famD`, `num_layoutsByPublicReading`
(Johnson/Prover/At/LawsAt.lean, ToldAt.lean): where the test of the copy's number says yes at a
proof file's string, the string's front bears that number.

Main names.
  `copy_of_num_fullD`, `copy_of_num_famD` (namespace `VerifiableInference.OnPublicFiles`)   for all data:
      at the input of the full size; at the told record of a family
  `copy_of_num_layoutsByPublicReading` (namespace `FlashProve`)   the call at the letters S of one set of public
      files

Limits. The test is `numCopy` (Johnson/Top/Fire/Code/PvFrontNum.lean), which decides that equation:
so this is its text, read. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.ToldAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁)
open OnBytes.K.Arm.Pub (D8)

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}

theorem copy_of_num_fullD
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)
    (hn : T.num = PV.Front.numCopy) (copy : ℕ)
    (π : OneProtocolProof 256 (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
                  silP runP).batch)
    (h : (innerCompilerInputAtFullSize T).seedQueries.num copy π.plains = true) :
    (pls₁ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP) π).1.copy = copy := by
  have h' : T.num copy π.plains = true := h
  rw [hn] at h'
  exact of_decide_eq_true h'

set_option maxRecDepth 20000 in
theorem copy_of_num_famD
    {T₀ : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P}
    (U : FamLettersD T₀) (d : D8) (hn : T₀.num = PV.Front.numCopy) (copy : ℕ)
    (π : OneProtocolProof 256 (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
                  silP runP).batch)
    (h : ((toldFamD U).Sd d).num copy π.plains = true) :
    (pls₁ (wholeDesc (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty silP
      runP) π).1.copy = copy :=
  copy_of_num_fullD (lettersFamD U d) hn copy π h

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open _root_.Iop (Dig)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁)
open OnBytes.K.Arm.Pub (D8)

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256)) (d : D8)

set_option maxRecDepth 20000 in
theorem copy_of_num_layoutsByPublicReading (copy : ℕ)
    (π : OneProtocolProof 256 (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
                  ByteArray.empty silP S.runP).batch)
    (h : ((S.layoutsByPublicReading c₀ m₀).Sd d).num copy π.plains = true) :
    (pls₁ (wholeDesc (ckP .two) (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2)
      ByteArray.empty silP S.runP) π).1.copy = copy :=
  copy_of_num_famD (LPFD.Full.famD S.A S.E S.G S.DK S.DP S.runK S.runP S.dec S.P S.hStar S.it
    Zk.pol Zk.KL Zk.lay S.sR S.hDK S.hDP S.hK S.N S.d₀ (c₀, m₀)) d (num_tOf S c₀ m₀) copy π h

end FlashProve
