-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/ZeroRunAtBytes.lean: the chance of the exception ZeroRun at flashProveAtFiles, and UndoUpTo from it.

1.  WHAT IS CLAIMED: at the format's starts, for provers that send their run values: over all coins, under every hash function, one of the six run
    values of the key's offline string and the online string is refused by the format with chance at most
    2 · 2^-256 and the coins' two chances: γ written out. The parser's premise UndoOnBut at ZeroRun then gives UndoUpTo at that γ.
2.  The salts' part is the coins' law; the further values' part is what the coins fix, read back through the strings' plain parts.
3.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.Face.BytesOfSide
import Johnson.CompletenessAndZeroKnowledge.ZeroRunMass
import Johnson.CompletenessAndZeroKnowledge.ReadsAtPlug
import Johnson.CompletenessAndZeroKnowledge.UndoUpToOfBut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Rom _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles OnBytes.WholeKey OnBytes.FrontRoad OnBytes.Prover
open VerifierAndGoals FlashProve FlashProve
open AtPublicFiles.AtFiles
open Johnson.Face
open TypedOracleCompiler.Joined (pls₂ pls₃)
open _root_.Run (bitsToBytes whole)
open Prob
open IntegerTransformer (Settings)

/-- Salts that the format refuses. -/
def refusedSalts : Set Rom.Bits := {salt | Fmt.runOk (bitsToBytes salt) ≠ true}

/-- The format refuses one string of 256 bits at most. -/
theorem refusedSalts_unique {n : ℕ} (hn : n = 256) (a b : Fin n → Bool) (ha : List.ofFn a ∈ refusedSalts)
    (hb : List.ofFn b ∈ refusedSalts) : a = b := by
  have zero : ∀ {c : Fin n → Bool}, List.ofFn c ∈ refusedSalts → bitsToBytes (List.ofFn c) = Fmt.zero32 := fun {c} hc => by
    by_contra hne
    exact hc (decide_eq_true hne)
  have wh : ∀ c : Fin n → Bool, whole (List.ofFn c) = true := fun c => by
    subst hn
    simp [whole]
  exact List.ofFn_injective (OnBytes.K.Arm.bitsToBytes_inj (wh a) (wh b) ((zero ha).trans (zero hb).symm))

/-- Run values that the format refuses. -/
def RefusedRuns (runs : FormatRuns) : Prop := ¬ (Fmt.runOk runs.1 = true ∧ Fmt.runOk runs.2 = true)

variable (files : PublicFiles) (settings : Settings) (fallbackInstance : (flashProveDescription.C files).X)
  (provers : HonestProvers (FlashProtocol files)) (rounds : FormatRounds)
  (runsOffline : provers.offlineProver.Coin → FormatRuns) (runsOnline : provers.onlineProver.Coin → FormatRuns)
  (linkRuns : FormatRuns) (limits : SearchLimits) (slotSalts : RequestLeafSaltLayout)

/-- **THE MASS OF ZeroRun AT flashProveAtFiles.** -/
theorem zeroRun_mass
    (hS : SendsItsRunValues provers (pvStarts files provers rounds runsOffline runsOnline linkRuns) fun _ => True)
    {εOffline εOnline : ℝ≥0∞}
    (massOffline : pr (unif provers.offlineProver.Coin) {κ | RefusedRuns (runsOffline κ)} ≤ εOffline)
    (massOnline : pr (unif provers.onlineProver.Coin) {κ | RefusedRuns (runsOnline κ)} ≤ εOnline)
    (i : (flashProveDescription.input files allZeroDigest []).Index) (x : (flashProveDescription.input files allZeroDigest []).Instance) :
    ZKCP.Pr (badExp (readOne (layoutsOfBuiltDescription flashProveData allZeroDigest [] files)
        (flashSide files settings fallbackInstance provers
          (pvStarts files provers rounds runsOffline runsOnline linkRuns) limits slotSalts)) i x ())
        (fun _ => {o | ZeroRun (dataAtFiles flashProveData files) allZeroDigest [] o.1.1.2 o.2}) ≤
      (((2 : ℝ≥0∞) ^ 256)⁻¹ + εOffline) + (((2 : ℝ≥0∞) ^ 256)⁻¹ + εOnline) := by
  refine le_trans (MeasureTheory.lintegral_mono fun f => MeasureTheory.measure_mono fun o ho => ?_)
    (flash_bad_mass files settings fallbackInstance provers
      (pvStarts files provers rounds runsOffline runsOnline linkRuns) limits slotSalts
      (fun reading => runValuesAreSent_formatStarts _ _ _ _ _ _ _ _ _ hS)
      (fun reading => readsThroughNonces_pv files settings fallbackInstance provers rounds runsOffline runsOnline
        linkRuns limits slotSalts reading)
      refusedSalts (refusedSalts_unique rfl)
      (fun a => RefusedRuns (pvKey (dataAtFiles flashProveData files).DK (dataAtFiles flashProveData files).G.rec₀ a.plains))
      (fun b => RefusedRuns (pvZ files (dataAtFiles flashProveData files).P b.plains)) RefusedRuns (fun _ h => h) (fun _ h => h)
      massOffline massOnline i x)
  rcases ho with ⟨a, ha, hn⟩ | ⟨b, hb, hn⟩
  · refine Or.inl ⟨a, ha, ?_⟩
    by_cases h1 : Fmt.runOk (bitsToBytes a.salt) = true
    · exact Or.inr fun h => hn ⟨h1, h.1, h.2⟩
    · exact Or.inl h1
  · refine Or.inr ⟨b, hb, ?_⟩
    by_cases h1 : Fmt.runOk (bitsToBytes b.salt) = true
    · exact Or.inr fun h => hn ⟨h1, h.1, h.2⟩
    · exact Or.inl h1

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.refusedSalts_unique
#print axioms VerifiableInference.Compilation.zeroRun_mass
