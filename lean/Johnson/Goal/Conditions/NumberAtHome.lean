-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/NumberAtHome.lean: AT THE CAPS OF 2^(work + 6) TRIES
(capT, capL, capB, Johnson/Goal/Conditions/HonestNumber.lean), in scope, where protocolDataWellFormed says yes: the
searches' part of completeness' number (alphaAll, Johnson/Prover/All/Law.lean) is at most
71 · 2^-92, and the three caps fit a word of 64 bits.

Main names.
  tested_key, tested_proof, tested_copy   BY LEAN's KERNEL at the written lists: 4 + 10 + 5, 31 + 10
    + 5 and 6 rounds have a test: 71.
  work_key, work_proof, work_copy   by the kernel: no round's test has more than 32 bits.
  failT_written, failL_written, failB_written   capFail at the three wire records, at letters S
    whose data are the written data.
  capT_lt, capL_lt, capB_lt   the caps are below 2^64 there.
  number_home   «number»: alphaAll at the input on which the members of theWider stand ≤ 71 · 2^-92
    + (ζ₁ + ζ₂) + (δT + δL + δB).
  caps_home     the three caps there.

Limits. THE CAPS ARE OF OUR CHOOSING. protocolDataWellFormed is a premise. That alphaAll bounds the honest side's
failure is another file's. 71 · 2^-92 is about 2^-85.85.
Local letter (notation of this file alone). ℌ: the compiler's input Description.input
  (Description.reBound flashProveDescription b) Z allZeroDigest [].
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HonestAtHome
import Johnson.Prover.Law.CapFailAt
import Johnson.Prover.All.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (KF)
open PV.EntryFive (dsF xsF)
open Johnson.G (writtenKFull writtenPFull writtenKFull_eq writtenPFull_eq dKeyFull dProofFull sumE
  sumE_eq)

/-! ## By the kernel, at the written lists -/

/-- The number of rounds with a test, in the form that the kernel evaluates. -/
def testedE (l : List ℕ) : ℕ := sumE 0 (l.map fun b => if b = 0 then 0 else 1)

theorem tested_of {l : List ℕ} {n : ℕ} (h : testedE l = n) : tested l = n := by
  rw [← h]
  unfold testedE tested
  rw [sumE_eq, Nat.zero_add]

/-- Every entry is at most 32, as a test that the kernel evaluates. -/
def le32 (l : List ℕ) : Bool := sumE 0 (l.map fun b => if b ≤ 32 then 0 else 1) == 0

theorem le32_mem : ∀ {l : List ℕ}, (l.map fun b => if b ≤ 32 then 0 else 1).sum = 0 →
    ∀ b ∈ l, b ≤ 32
  | [], _, _, h => absurd h (List.not_mem_nil)
  | a :: l, h, b, hb => by
    rw [List.map_cons, List.sum_cons] at h
    rcases List.mem_cons.1 hb with e | hb'
    · rw [e]
      by_contra hc
      rw [if_neg hc] at h
      omega
    · exact le32_mem (by omega) b hb'

theorem le32_of {l : List ℕ} (h : le32 l = true) : ∀ b ∈ l, b ≤ 32 := by
  unfold le32 at h
  rw [sumE_eq, Nat.zero_add] at h
  exact le32_mem (beq_iff_eq.1 h)

theorem tested_key1 : testedE (dKeyFull.ds₁.map (·.entry.work)) = 4 := by decide +kernel
theorem tested_key2 : testedE (dKeyFull.ds₂.map (·.entry.work)) = 10 := by decide +kernel
theorem tested_key3 : testedE (dKeyFull.ds₃.map (·.entry.work)) = 5 := by decide +kernel
theorem tested_proof1 : testedE (dProofFull.ds₁.map (·.entry.work)) = 31 := by decide +kernel
theorem tested_proof2 : testedE (dProofFull.ds₂.map (·.entry.work)) = 10 := by decide +kernel
theorem tested_proof3 : testedE (dProofFull.ds₃.map (·.entry.work)) = 5 := by decide +kernel
theorem tested_copy : testedE (dsF.map (·.entry.work)) = 6 := by decide +kernel

theorem work_key1 : le32 (dKeyFull.ds₁.map (·.entry.work)) = true := by decide +kernel
theorem work_key2 : le32 (dKeyFull.ds₂.map (·.entry.work)) = true := by decide +kernel
theorem work_key3 : le32 (dKeyFull.ds₃.map (·.entry.work)) = true := by decide +kernel
theorem work_proof1 : le32 (dProofFull.ds₁.map (·.entry.work)) = true := by decide +kernel
theorem work_proof2 : le32 (dProofFull.ds₂.map (·.entry.work)) = true := by decide +kernel
theorem work_proof3 : le32 (dProofFull.ds₃.map (·.entry.work)) = true := by decide +kernel
theorem work_copy : le32 (dsF.map (·.entry.work)) = true := by decide +kernel

/-- The key file's counts and bounds at data that are the written data. -/
theorem tested_key (D : WholeD) (e : D = writtenKFull) :
    (tested (D.ds₁.map (·.entry.work)) = 4 ∧ tested (D.ds₂.map (·.entry.work)) = 10 ∧
      tested (D.ds₃.map (·.entry.work)) = 5) ∧
    ((∀ b ∈ D.ds₁.map (·.entry.work), b ≤ 32) ∧ (∀ b ∈ D.ds₂.map (·.entry.work), b ≤ 32) ∧
      ∀ b ∈ D.ds₃.map (·.entry.work), b ≤ 32) := by
  have e' : D = dKeyFull := e.trans writtenKFull_eq
  subst e'
  exact ⟨⟨tested_of tested_key1, tested_of tested_key2, tested_of tested_key3⟩,
    le32_of work_key1, le32_of work_key2, le32_of work_key3⟩

/-- The proof file's. -/
theorem tested_proof (D : WholeD) (e : D = writtenPFull) :
    (tested (D.ds₁.map (·.entry.work)) = 31 ∧ tested (D.ds₂.map (·.entry.work)) = 10 ∧
      tested (D.ds₃.map (·.entry.work)) = 5) ∧
    ((∀ b ∈ D.ds₁.map (·.entry.work), b ≤ 32) ∧ (∀ b ∈ D.ds₂.map (·.entry.work), b ≤ 32) ∧
      ∀ b ∈ D.ds₃.map (·.entry.work), b ≤ 32) := by
  have e' : D = dProofFull := e.trans writtenPFull_eq
  subst e'
  exact ⟨⟨tested_of tested_proof1, tested_of tested_proof2, tested_of tested_proof3⟩,
    le32_of work_proof1, le32_of work_proof2, le32_of work_proof3⟩

/-! ## The sums of terms -/

/-- A list of rounds with n tests. -/
theorem sum_fail_le {α : Type} (wk : α → ℕ) (l : List α) (n : ℕ) (h : tested (l.map wk) = n) :
    (l.map fun d => failAt (wk d)).sum ≤ (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 92)⁻¹ := by
  have e : (l.map fun d => failAt (wk d)) = (l.map wk).map failAt := by
    rw [List.map_map]
    rfl
  rw [e, ← h]
  exact sum_failAt_le _

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c₀ : Digest) (m₀ : List (Dig 256))

/-- The copy's file's searches. -/
theorem failL_written :
    capFail (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.link.shape (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).linkRoundSplits
      (wLC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout).sh capL 0 ≤ 6 * ((2 : ℝ≥0∞) ^ 92)⁻¹ :=
  (le_of_eq (capFail_wqW (ckP .two) (KF S.DK S.DP) (chalP .two (KF S.DK S.DP)) dsF frS.P.T.a xsF
    S.dec)).trans (sum_fail_le (·.entry.work) dsF 6 (tested_of tested_copy))

/-- The key file's searches. -/
theorem failT_written (eK : S.DK = writtenKFull) :
    capFail (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.offline.shape (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).offlineRoundSplits
      (wTC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout).sh (capT S) 0 ≤ 19 * ((2 : ℝ≥0∞) ^ 92)⁻¹ := by
  have t := (tested_key S.DK eK).1
  refine (le_of_eq (capFail_wqWhole (ckP .two) (KF S.DK S.DP) (chalP .two (KF S.DK S.DP))
    (S.DK.at frS.P.T.a) (front₀ S.G.rec₀) (join₀ S.G.rec₀) ByteArray.empty silK S.runK)).trans ?_
  refine (add_le_add (add_le_add (sum_fail_le (·.entry.work) S.DK.ds₁ 4 t.1)
    (sum_fail_le (·.entry.work) S.DK.ds₂ 10 t.2.1))
    (sum_fail_le (·.entry.work) S.DK.ds₃ 5 t.2.2)).trans (le_of_eq ?_)
  rw [← add_mul, ← add_mul]
  norm_num

/-- The proof file's searches. -/
theorem failB_written (eP : S.DP = writtenPFull) :
    capFail (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.onlineBatch.loc.shape
      (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).protocol.onlineBatch.ann (wBC (innerCompilerInputAtFullSize (S.inputFieldsAtReadings c₀ m₀)).queryLayout).sh (capB S)
      0 ≤ 46 * ((2 : ℝ≥0∞) ^ 92)⁻¹ := by
  have t := (tested_proof S.DP eP).1
  refine (le_of_eq (capFail_wqWhole (ckP .two) (KF S.DK S.DP) (chalP .two (KF S.DK S.DP))
    (S.DP.at frS.P.T.a) (front₀ S.G.z₀.2) (join₀ S.G.z₀.2) ByteArray.empty silP S.runP)).trans ?_
  refine (add_le_add (add_le_add (sum_fail_le (·.entry.work) S.DP.ds₁ 31 t.1)
    (sum_fail_le (·.entry.work) S.DP.ds₂ 10 t.2.1))
    (sum_fail_le (·.entry.work) S.DP.ds₃ 5 t.2.2)).trans (le_of_eq ?_)
  rw [← add_mul, ← add_mul]
  norm_num

/-! ## The caps fit a word -/

theorem capAt_lt (work : ℕ → ℕ) (h : ∀ j, work j ≤ 32) (j : ℕ) : capAt work j < 2 ^ 64 := by
  unfold capAt
  have h1 : 2 ^ (work j + 6) ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) (by have := h j; omega)
  have h2 : (2 : ℕ) ^ 38 < 2 ^ 64 := by norm_num
  omega

/-- Page.workAt is an entry's work, or 0. -/
theorem workAt_le (D : WholeD) (h₁ : ∀ b ∈ D.ds₁.map (·.entry.work), b ≤ 32)
    (h₂ : ∀ b ∈ D.ds₂.map (·.entry.work), b ≤ 32) (h₃ : ∀ b ∈ D.ds₃.map (·.entry.work), b ≤ 32)
    (j : ℕ) : Page.workAt D j ≤ 32 := by
  have key : ∀ (l : List RDT) (k : ℕ), (∀ b ∈ l.map (·.entry.work), b ≤ 32) →
      ((l[k]?).map (·.entry.work)).getD 0 ≤ 32 := by
    intro l k hl
    cases hk : l[k]? with
    | none => exact Nat.zero_le _
    | some d => exact hl _ (List.mem_map.2 ⟨d, List.mem_of_getElem? hk, rfl⟩)
  unfold Page.workAt Page.rdAt
  split_ifs
  · exact Nat.zero_le _
  · exact key _ _ h₁
  · exact Nat.zero_le _
  · exact key _ _ h₂
  · exact Nat.zero_le _
  · exact key _ _ h₃

theorem capT_lt (eK : S.DK = writtenKFull) (j : ℕ) : capT S j < 2 ^ 64 :=
  capAt_lt _ (workAt_le (S.DK.at frS.P.T.a) (tested_key S.DK eK).2.1 (tested_key S.DK eK).2.2.1
    (tested_key S.DK eK).2.2.2) j

theorem capB_lt (eP : S.DP = writtenPFull) (j : ℕ) : capB S j < 2 ^ 64 :=
  capAt_lt _ (workAt_le (S.DP.at frS.P.T.a) (tested_proof S.DP eP).2.1
    (tested_proof S.DP eP).2.2.1 (tested_proof S.DP eP).2.2.2) j

theorem capL_lt (j : ℕ) : capL j < 2 ^ 64 :=
  capAt_lt _ (fun k => by
    unfold workL
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      rw [List.getD_cons_succ]
      rcases Nat.lt_or_ge k (dsF.map (·.entry.work)).length with h | h
      · rw [List.getD_eq_getElem _ _ h]
        exact le32_of work_copy _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]
        exact Nat.zero_le _) j

end FlashProve

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.Prover (alphaAll)

/- Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- the input there -/
local notation "ℌ" => Description.input (Description.reBound flashProveDescription b) Z allZeroDigest []

/-- **«number» at these caps.** -/
theorem number_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (ζ₁ ζ₂ δT δL δB : ℝ≥0∞) :
    alphaAll (ℌ).queryLayout (capT (sAt Z)) capL (capB (sAt Z)) ζ₁ ζ₂ δT δL δB ≤
      71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + (ζ₁ + ζ₂) + (δT + δL + δB) := by
  unfold alphaAll
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  refine (add_le_add (add_le_add
    (failT_written (sAt Z) allZeroDigest [] (key_built_written Z scope live))
    (failL_written (sAt Z) allZeroDigest []))
    (failB_written (sAt Z) allZeroDigest [] (proof_built_written Z scope live))).trans (le_of_eq ?_)
  rw [← add_mul, ← add_mul]
  norm_num

/-- **The three caps fit a word of 64 bits.** -/
theorem caps_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (∀ j, capT (sAt Z) j < 2 ^ 64) ∧ (∀ j, capL j < 2 ^ 64) ∧ ∀ j, capB (sAt Z) j < 2 ^ 64 :=
  ⟨capT_lt (sAt Z) (key_built_written Z scope live), capL_lt,
    capB_lt (sAt Z) (proof_built_written Z scope live)⟩

end FlashProve

#print axioms FlashProve.tested_of
#print axioms FlashProve.le32_mem
#print axioms FlashProve.le32_of
#print axioms FlashProve.tested_key1
#print axioms FlashProve.tested_key2
#print axioms FlashProve.tested_key3
#print axioms FlashProve.tested_proof1
#print axioms FlashProve.tested_proof2
#print axioms FlashProve.tested_proof3
#print axioms FlashProve.tested_copy
#print axioms FlashProve.work_key1
#print axioms FlashProve.work_key2
#print axioms FlashProve.work_key3
#print axioms FlashProve.work_proof1
#print axioms FlashProve.work_proof2
#print axioms FlashProve.work_proof3
#print axioms FlashProve.work_copy
#print axioms FlashProve.tested_key
#print axioms FlashProve.tested_proof
#print axioms FlashProve.sum_fail_le
#print axioms FlashProve.failL_written
#print axioms FlashProve.failT_written
#print axioms FlashProve.failB_written
#print axioms FlashProve.capAt_lt
#print axioms FlashProve.workAt_le
#print axioms FlashProve.capT_lt
#print axioms FlashProve.capB_lt
#print axioms FlashProve.capL_lt
#print axioms FlashProve.number_home
#print axioms FlashProve.caps_home
