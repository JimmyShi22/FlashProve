-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAsIOPStopsAtBase.lean: the debts bad and hid of completeness at famG, from a bound on
sets written at the base prover: the prover that the term's reads through. A file bounds its stops
there, and crosses once. It states no goal.

  baseBad, baseHid   the two abort sets of the family, written at the base prover: the public one
                     with the shared chain's stop.
  famBC_bad_base, famBC_hid_base   the family's sets at the rows' prover are these.
  badSmall_at_base, hidSmall_at_base   BadSmall and HidSmall at famG.

By what. honestBC_bad_rows, honestBC_hid_rows, honestBC_stop0_rows (E2E/ThruYesBase.lean), and the
unfolding of famG to honestProversByCopyNumber and of BatchHonestProver.one (Iop/Batch.lean).

Limits. hrows and hk are premises. Nothing is said of how large these sets are.
-/
import E2E.ThruYesBase
import E2E.BridgeJoinAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Bridge
open Iop Prob AtPublicFiles.Along
open OnBytes.Maker (WholeD)
open _root_.Run.PQ (CK SgX)
open ProofFile.Honest (batchOf honestBatchProverOfFile Prover KeyAndJoiningRoundMessages ProverCoinCounts Sides drawsLo drawsSh Committer badB hidB stop0B)

section Base
variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Sc Xc TF TJ T3 R₂ R₃ : Type} (C : CK) (D : WholeD)
  (tF : TF) (tJ : TJ) (t3 : T3) (F : VerifiableInference.Desc.FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool)

/-- The public abort set of the family, written at the prover H: a public stop of the online rounds,
or a stop of the shared chain. -/
def baseBad (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Set (Rho (batchOf C D tF tJ t3 F silent).loc.shape) :=
  {ρ | badB F H (drawsLo C D tF tJ t3 (Rho.lo (batchOf C D tF tJ t3 F silent).ann ρ)) = true ∨
    stop0B F H (drawsSh C D tF tJ t3 (Rho.sh (batchOf C D tF tJ t3 F silent).ann ρ)) = true}

/-- The abort set of the family that reads the private input, written at the prover H. -/
def baseHid (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀) (rc : Rc) (x : Xi) :
    Set (Rho (batchOf C D tF tJ t3 F silent).loc.shape) :=
  {ρ | hidB F H w rc x (drawsLo C D tF tJ t3 (Rho.lo (batchOf C D tF tJ t3 F silent).ann ρ)) = true}

variable (B : ProverCoinCounts) (G : Sides F B W₀' Rc' Ky Tr X₀ X)
  (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (Cm : Committer W₀' Rc' Sc Xc Xi Ky) (item₀ : ℕ)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
  (J : ℕ → R₂ → R₃ → KeyAndJoiningRoundMessages W₀' Rc' Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀' × Rc' × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)
  (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
include hrows hk

/-- The family's public abort set at the rows' prover is that at the base prover. -/
theorem famBC_bad_base :
    (honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) J sh ext).Bad =
      baseBad C D tF tJ t3 F silent H := by
  ext ρ
  show (Rho.lo (batchOf C D tF tJ t3 F silent).ann ρ ∈
      (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J 0) sh
        ext).Bad ∨
      (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J 0) sh
        ext).stop0 (Rho.sh (batchOf C D tF tJ t3 F silent).ann ρ) = true) ↔ _
  rw [honestBC_bad_rows C D tF tJ t3 F silent B G g rd d Cm item₀ H sh ext (J 0) hrows hk,
    honestBC_stop0_rows C D tF tJ t3 F silent B G g rd d Cm item₀ H sh ext (J 0) hrows hk]
  rfl

/-- The same of the abort set that reads the private input. -/
theorem famBC_hid_base (n : ℕ) (w : W₀' × Rc' × Sd) (x : Xi) :
    ((honestProversByCopyNumber C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) J sh ext).at
      n).Hid w x = baseHid C D tF tJ t3 F silent H (g w.1) (rd w.2.1) x := by
  ext ρ
  show Rho.lo (batchOf C D tF tJ t3 F silent).ann ρ ∈
      (honestBatchProverOfFile C D tF tJ t3 F silent B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) (J n) sh
        ext).Hid w x ↔ _
  rw [honestBC_hid_rows C D tF tJ t3 F silent B G g rd d Cm item₀ H sh ext (J n) hrows hk w x]
  rfl

end Base

end AtPublicFiles.Bridge

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open OnBytes.Slice (frS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open P5J

local instance (priority := high) nonemptyPadZ_stopsAtBase : Nonempty PadZ := pads_nonempty frS 402653181

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh W₀ Rc : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (g : FullSizeMatrix → W₀) (rd : (protocolAtFiles Z).EncodingRandomness → Rc) (d : FullSizeMatrix)
  (H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Xh)
  (hrows : G.prover (H.thru g rd d) = H.thru g rd d)
  (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = H.key)
include hrows hk

/-- **BadSmall at famG, from a bound at the base prover.** -/
theorem badSmall_at_base {zB : ℝ≥0∞}
    (h : prRho (baseBad (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst H) ≤ zB) :
    BadSmall (famG Z Zp Np cF run₂ run₃ B G (H.thru g rd d)) zB :=
  (le_of_eq (congrArg prRho
    (famBC_bad_base (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B G g rd d
      (cmAlong (AZ Z) PadZ (holdZ Z)) 0 H (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) hrows
      hk))).trans h

/-- **HidSmall at famG, from a bound at the base prover.** -/
theorem hidSmall_at_base {Td} {z : ℝ≥0∞}
    (h : ∀ n w a, Td n w a →
      prRho (baseHid (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst H (g w.1)
        (rd w.2.1) (instanceAsPlainRecord a)) ≤ z) :
    HidSmall (famG Z Zp Np cF run₂ run₃ B G (H.thru g rd d)) Td z :=
  fun n w a hx => (le_of_eq (congrArg prRho
    (famBC_hid_base (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B G g rd d
      (cmAlong (AZ Z) PadZ (holdZ Z)) 0 H (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z) hrows hk
      n w (instanceAsPlainRecord a)))).trans (h n w a hx)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.badSmall_at_base
#print axioms AtPublicFiles.AtFiles.hidSmall_at_base
