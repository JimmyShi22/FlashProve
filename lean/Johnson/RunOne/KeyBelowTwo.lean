-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyBelowTwo.lean: THE WRITTEN ERRORS OF THE KEY FILE's SHARED CHAIN's TWO SENDINGS (o_u with the first mask; o_omega with o_sp), AT THE SENDING KIND's OWN COUNT errPort AT THE RADII OF THE TABLES' LIST OF SIX, ARE SHARES OF AT MOST 2^-128 OF THE ROUND's VERIFIER MESSAGES; NO BIT OF THE 128 IS PROOF OF WORK. Statements with proofs: evaluations in the kernel on written values, and calls of powB_send (Johnson/Desc/K1/Law/PowB.lean) and seeds_one (GoodSend4.lean). IT PAYS NO FIELD OF THE KEY FILE's TABLES.
OBJECT. sendPiece's errors at PU bp | PO bp: the sending kind's parameters at p14Key bp (Johnson/RunOne/KeyRowsInScope.lean). USER. The calls of rows 2.2 and 2.5 of the tables over keeps₂_send2_seat | _send5_seat (Johnson/RunOne/KeyRowsBackAtSeat.lean), at e := errPort: what Err.le_cap_of_below_inv 128 and keeps_same_cap ask.
LETTERS. bp (what stands before the point: not read); b base d₁ d₂, any block, base and two written rounds. PREMISES of the two ends: the first written round bears the place's own entry of seeds and the kind "seeds".

  PU, PO, rU, rO: the two places and their radii.
  pu_is, po_is: at every bp the place is the one at pFull (KeyCondThree.lean).
  pow_u_full, pow_omega_full: the comparison powB at 128: by the kernel. pow_u_no, pow_omega_no: negative tests: at a level that is plainly too large, 100000, it says no: the comparison can fail.
  pow_u_edge, pow_omega_edge: the sharp edges: yes at 175 | 172, no at 176 | 173: by the kernel. (Where to look was learnt from a file of evaluations, not named here; the theorems are the kernel's.)
  work_u_full, work_omega_full: the places bear no proof of work: parK1's work is P.set.workOf .sample P.scope (Johnson/Desc/K14/Blocks.lean; OnBytes/Params/Setting.lean): 0 at the written setting, by the kernel. powB's right side bears the factor 2 ^ work: here 1.
  cond_u_key, cond_omega_key, seeds_u_key, seeds_omega_key: condPort and "one seed" at every bp.
  below_u_key, below_omega_key: the ends. below_u_at, below_omega_at: the same at p14At X P where the sized key is the written one.
THE TWO STRINGS are the base's own literals, lifted. THE THREE RADII are the last three of the list of six (six_345, KeyCondThree.lean).
WHAT IT DOES NOT SAY. One count a round; no sum over rounds. That a count bounds a cheating prover's chance is the law's. Nothing on the round behind the seeds, which draws nothing. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.KeyCondThree
import Johnson.Desc.K1.Law.PowB
import Johnson.Desc.K1.Law.GoodSend4

set_option autoImplicit false

namespace Johnson.RunOne.KeyMsg

open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps Johnson.RunOne.KeySendGood
open VerifiableInference.Desc (Block noDigest viewWordsBelowPrime roundsFit)
open VerifiableInference.Desc.Sound (held)
open VerifiableInference.Desc.Plain (held_decide)
open VerifiableInference.Desc.Keeps (ebind_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (Par SeedIs Tie Seeds ReadsAs decideSend shapesOf shapeAt sampledAt condPort seedIs_behind_len draw_len SameMsgs)
open LPFD (Reached Hist₁ Hist₃)
open Johnson.Pack (bitsZ)

open Lk6.AtPlan (keyFull)
open Johnson.RunOne.KeyRows23 (p14At p14Key)
open _root_.Desc.K14 (P14 parK1 withU withOmega)
open VerifiableInference.Desc.K1 (powB powB_send seeds_one errPort sendPiece seedEntry)
open VerifiableInference.Desc.Sound (Frame)
open OnBytes.Maker (RDT)
open _root_.Iop (Err)
open scoped ENNReal

/-- The sending kind's parameters at "send o_u". -/
abbrev PU (bp : List (ℕ × ℕ)) : Par := parK1 (p14Key bp) 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])
/-- … and at "send o_omega". -/
abbrev PO (bp : List (ℕ × ℕ)) : Par := parK1 (p14Key bp) 5 "o_omega and o_sp" (withOmega keyFull.once.shape)
abbrev rU : ℕ → ℕ := fun _ => 8342420
abbrev rO : ℕ → ℕ := fun k => if k = 0 then 3138896 else 6130

theorem pu_is (bp : List (ℕ × ℕ)) : PU bp = parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[]) := by
  show parK1 (p14Key bp) _ _ _ = _
  rw [p14Key_eta]
  rfl

theorem po_is (bp : List (ℕ × ℕ)) : PO bp = parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape) := by
  show parK1 (p14Key bp) _ _ _ = _
  rw [p14Key_eta]
  rfl

theorem pow_u_full : powB (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])) rU 128 = true := by
  decide +kernel
/-- A negative test. -/
theorem pow_u_no : powB (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])) rU 100000 = false := by
  decide +kernel
theorem pow_omega_full : powB (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape)) rO 128 = true := by
  decide +kernel
/-- A negative test. -/
theorem pow_omega_no : powB (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape)) rO 100000 = false := by
  decide +kernel

/-- The sharp edges: the last level at which the comparison says yes, and the first at which it says no. -/
theorem pow_u_edge : powB (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])) rU 175 = true ∧
    powB (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])) rU 176 = false := by decide +kernel
theorem pow_omega_edge : powB (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape)) rO 172 = true ∧
    powB (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape)) rO 173 = false := by decide +kernel

theorem work_u_full : (parK1 pFull 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])).work = 0 := by decide +kernel
theorem work_omega_full : (parK1 pFull 5 "o_omega and o_sp" (withOmega keyFull.once.shape)).work = 0 := by decide +kernel

theorem cond_u_key (bp : List (ℕ × ℕ)) : condPort (PU bp) rU = true := by
  rw [pu_is]
  exact cond_u_full

theorem cond_omega_key (bp : List (ℕ × ℕ)) : condPort (PO bp) rO = true := by
  rw [po_is]
  exact cond_omega_full

theorem seeds_u_key (bp : List (ℕ × ℕ)) : (PU bp).seeds = 1 := seeds_one _ _ (cond_u_key bp)
theorem seeds_omega_key (bp : List (ℕ × ℕ)) : (PO bp).seeds = 1 := seeds_one _ _ (cond_omega_key bp)

/-- **Row 2.2's sending: its written errors lie at or below 2^-128.** -/
theorem below_u_key (bp : List (ℕ × ℕ)) {T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (PU bp)) (hk₁ : d₁.kind = .seeds) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ (PU bp).coordinates (errPort (PU bp) rU)).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  powB_send (PU bp) (seeds_u_key bp) rU 128 (by rw [pu_is]; exact pow_u_full) b base d₁ d₂ he₁ hk₁

/-- **Row 2.5's.** -/
theorem below_omega_key (bp : List (ℕ × ℕ)) {T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (PO bp)) (hk₁ : d₁.kind = .seeds) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂ (PO bp).coordinates (errPort (PO bp) rO)).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  powB_send (PO bp) (seeds_omega_key bp) rO 128 (by rw [po_is]; exact pow_omega_full) b base d₁ d₂ he₁ hk₁

variable {X : Source} {P : LaterPlaces}

/-- The same at the key file's own parameters, where the sized key is the written one. -/
theorem below_u_at (hkey : X.chains.made.sized.key = keyFull) {T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ)
    (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (parK1 (p14At X P) 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])))
    (hk₁ : d₁.kind = .seeds) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂
      (parK1 (p14At X P) 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])).coordinates
      (errPort (parK1 (p14At X P) 2 "o_u and the first mask" ((withU keyFull.once.shape).getD #[])) rU)).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [Johnson.RunOne.KeyRows23.p14At_key hkey P] at he₁ ⊢
  exact below_u_key _ b base d₁ d₂ he₁ hk₁

theorem below_omega_at (hkey : X.chains.made.sized.key = keyFull) {T Cl W : Type} {F : Frame} (b : Block T Cl) (base : ℕ)
    (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega keyFull.once.shape)))
    (hk₁ : d₁.kind = .seeds) :
    Err.Below (sendPiece (W := W) (F := F) b base d₁ d₂
      (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega keyFull.once.shape)).coordinates
      (errPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega keyFull.once.shape)) rO)).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  rw [Johnson.RunOne.KeyRows23.p14At_key hkey P] at he₁ ⊢
  exact below_omega_key _ b base d₁ d₂ he₁ hk₁

end Johnson.RunOne.KeyMsg

#print axioms Johnson.RunOne.KeyMsg.pu_is
#print axioms Johnson.RunOne.KeyMsg.po_is
#print axioms Johnson.RunOne.KeyMsg.pow_u_full
#print axioms Johnson.RunOne.KeyMsg.pow_u_no
#print axioms Johnson.RunOne.KeyMsg.pow_omega_full
#print axioms Johnson.RunOne.KeyMsg.pow_omega_no
#print axioms Johnson.RunOne.KeyMsg.pow_u_edge
#print axioms Johnson.RunOne.KeyMsg.pow_omega_edge
#print axioms Johnson.RunOne.KeyMsg.work_u_full
#print axioms Johnson.RunOne.KeyMsg.work_omega_full
#print axioms Johnson.RunOne.KeyMsg.cond_u_key
#print axioms Johnson.RunOne.KeyMsg.cond_omega_key
#print axioms Johnson.RunOne.KeyMsg.seeds_u_key
#print axioms Johnson.RunOne.KeyMsg.seeds_omega_key
#print axioms Johnson.RunOne.KeyMsg.below_u_key
#print axioms Johnson.RunOne.KeyMsg.below_omega_key
#print axioms Johnson.RunOne.KeyMsg.below_u_at
#print axioms Johnson.RunOne.KeyMsg.below_omega_at
