-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/HomeAt.lean: the lemmas on the told record at the letters S of the public files
(Johnson/Prover/At/ToldAt.lean, NumBack.lean) at the told record of the goals' description with its
number of coins laid anew: `((theTerms placeHolderCoins).T Z).reBound (b Z)` over the input
`(flashProveDescription.reBound b).input Z allZeroDigest []` (Johnson/Goal/Conditions/BindsAtThe.lean, ReBound.lean), b a
letter.

Main names.
  `wiresFit_reBound`, `lawFit_reBound` (namespace `VerifiableInference.OnPublicFiles`)   for every input
      and told record: laying the number of coins anew turns neither premise
  `wiresFit_home`, `lawFit_home`   `WiresFit` and `LawFit` there, at all public files, all readings
      and all caps: no premise
  `num_home`, `copy_of_num_home`   the test of the copy's number there says yes at a proof file's
      string if and only if the string's front bears that number
  `pub_det_home`   the public reading there returns, at every hash function, the pair
      (cAt Z hash, sevenAt Z hash)
  (the last five in the namespace `FlashProve`)

Limits. Calls: the told record there is `(dataAtFiles flashProveData Z).layoutsByPublicReading allZeroDigest []` but for the number of
coins, by unfolding. At public files where the frame's test says no the description lays data
without a round: the two records of premises hold there too and say little. Nothing here says that a
verifier says yes. Nothing on soundness or completeness.

Local letters (notation of this file alone). ℌ: the input Description.input (Description.reBound flashProveDescription
  b) Z allZeroDigest [] · 𝔗: the told record LayoutsByPublicReading.reBound (HonestTerms.T (theTerms placeHolderCoins) Z)
  (b Z).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.At.NumBack
import Johnson.Goal.Conditions.ReBound
import Johnson.Goal.Conditions.PlaceHolderCoins

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes.Prover (WiresFit LawFit)

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b : ℕ) (d : T.D)

theorem wiresFit_reBound (h : WiresFit R.queryLayout (T.cA d)) :
    WiresFit (R.reBound b).queryLayout ((T.reBound b).cA d) := h

theorem lawFit_reBound (capT capL capB : ℕ → ℕ) (h : LawFit R.queryLayout (T.Sd d) capT capL capB) :
    LawFit (R.reBound b).queryLayout ((T.reBound b).Sd d) capT capL capB := h

end VerifiableInference.OnPublicFiles

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (pls₁)
open OnBytes.Prover (WiresFit LawFit)

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
theorem wiresFit_home (d : (𝔗).D) : WiresFit (ℌ).queryLayout ((𝔗).cA d) :=
  wiresFit_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] d (Meaning.numbersFit_the Z)

set_option maxRecDepth 100000 in
theorem lawFit_home (d : (𝔗).D) (capT capL capB : ℕ → ℕ) :
    LawFit (ℌ).queryLayout ((𝔗).Sd d) capT capL capB :=
  lawFit_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] d (Meaning.numbersFit_the Z) capT capL capB

set_option maxRecDepth 100000 in
theorem num_home (d : (𝔗).D) (copy : ℕ) (π : OneProtocolProof 256 (ℌ).protocol.onlineBatch)
    (h : (pls₁ (wholeDesc (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty silP
      (dataAtFiles flashProveData Z).runP) π).1.copy = copy) :
    ((𝔗).Sd d).num copy π.plains = true :=
  num_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] d copy π h

set_option maxRecDepth 100000 in
theorem copy_of_num_home (d : (𝔗).D) (copy : ℕ) (π : OneProtocolProof 256 (ℌ).protocol.onlineBatch)
    (h : ((𝔗).Sd d).num copy π.plains = true) :
    (pls₁ (wholeDesc (ckP .two) ((dataAtFiles flashProveData Z).DP.at frS.P.T.a)
      (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty silP
      (dataAtFiles flashProveData Z).runP) π).1.copy = copy :=
  copy_of_num_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] d copy π h

set_option maxRecDepth 100000 in
theorem pub_det_home (hash : VerifiableInference.Hash) :
    (𝔗).Pub.det (famOne hash) = (cAt Z hash, sevenAt Z hash) :=
  pub_det_layoutsByPublicReading (dataAtFiles flashProveData) Z allZeroDigest [] hash

end FlashProve
