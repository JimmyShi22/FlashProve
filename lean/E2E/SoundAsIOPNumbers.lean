-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SoundAsIOPNumbers.lean: THE TWO NUMBERS OF SOUNDNESS AS AN IOP, AT EVERY PUBLIC FILES Z IN SCOPE WHERE
THE DESCRIPTION's OWN TESTS PASS, by evaluation in Lean's kernel; and the bound on a cheating prover's
probability there.

E2E/SoundAsIOPProbabilityAtFiles.lean bounds the probability that the conclusion of a whole run fails,
over uniform points and the challenges that pass the tests of proof of work, by
(number of rounds) * (2^(the largest work of a round) * 2^-128); of the two numbers it knows, at every Z:
work at most 64, rounds at most 2^20. In scope, where protocolDataWellFormed says yes, the rounds' data are the lists
written in Lean, whatever the eight free numbers of the parameter file are (key_built_written,
proof_built_written: Johnson/Goal/Description/). So there:

  `mostWorkInScope`      no round has more than 32 bits of work.
  `roundsInScope`        the whole run has 67,391 rounds: 18,951 offline, 42 in the link, 48,393 online,
                         and the five added ones (two points, two answers, the naming of a request).
  `probabilityInScope`   for every provers' fields P, every fill and every prover of the whole run: the
                         conclusion fails with probability at most 67391 * 2^-96.
  `probabilityInScope79`, `bound_le_79`, `bound_lt_one`   that is at most 2^-79, which is below 1.

How. In general, at every Z: the largest work is at most n if no round's data in the key file's three
lists, the link's list and the proof file's three lists has more (`mostWorkAtFiles_le_of`); the number
of rounds is the seven lists' lengths and twelve (`rounds_eq`). The written lists stand over twins that
the kernel evaluates (writtenKFull_eq, writtenPFull_eq); the seven tests on work are evaluated here, the
lengths in Johnson/Flat/Dec/FitAtWritten.lean and Johnson/Flat/ArmSibCount.lean.

Limits.
- Those of E2E/SoundAsIOPProbabilityAtFiles.lean and of E2E/SoundAsIOPAtFiles.lean: ONE WHOLE RUN (one first
  table, one copy, one request); soundness alone; before any hash; the relation is the object's relaxed
  one at the files' policy; a deterministic prover; under InScope, readFiles, protocolDataWellFormed. That these three
  have a member: AtFullSide/E2E/SoundAsIOPNumbersAtWritten.lean.
- 2^-96 IS THE BOUND OF THE WEAKEST KIND OF ROUND, laid on every round: 2^-128 with up to 32 bits of
  work taken back out. It is no figure for the compiled system, where the work is paid in hash queries.
- That some round has 32 bits of work, at every Z, is mostWorkAtFiles_ge
  (E2E/SoundAsIOPProbabilityAtFilesProofs.lean): so in scope, where protocolDataWellFormed says yes, the largest work is
  32, and 67391 * 2^-96 is what that file's bound gives there.
- THE NUMBER OF ROUNDS COUNTS EVERY ROUND, also those in which the verifier sends nothing: three in each
  whole file, the link's front round, three of the five added.
- The head of Johnson/Flat/Dec/FitAtWritten.lean says of its own file that the written lists being the
  plan's rounds is no theorem there. What is spent here is key_built_written and proof_built_written:
  that the data LAID in the description at such a Z are the written lists.
-/
import E2E.SoundAsIOPProbabilityAtFilesProofs
import Johnson.Flat.Dec.FitAtWritten
import Johnson.Flat.ArmSibCount
import Johnson.Goal.Description.KeyWritten
import Johnson.Goal.Description.ProofWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

/-! ## 1. The tests on work, evaluated -/

namespace Johnson.G
open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice _root_.Run _root_.Run.PQ

/-- No round of the list has more than b bits of work. -/
def workAtMost (b : ℕ) (ds : List RDT) : Bool :=
  ds.all fun d => decide (d.entry.work ≤ b)

theorem work_le_of_workAtMost {b : ℕ} {ds : List RDT} (h : workAtMost b ds = true) :
    ∀ d ∈ ds, d.entry.work ≤ b := by
  unfold workAtMost at h
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

/-- The three lists of a file's data together. -/
theorem work_le_of_three {b : ℕ} {D : WholeD} (h : workAtMost b D.ds₁ = true ∧
    workAtMost b D.ds₂ = true ∧ workAtMost b D.ds₃ = true) :
    ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.entry.work ≤ b := fun d hd =>
  (List.mem_append.1 hd).elim (work_le_of_workAtMost h.1 d) fun hd' =>
    (List.mem_append.1 hd').elim (work_le_of_workAtMost h.2.1 d) (work_le_of_workAtMost h.2.2 d)

set_option maxRecDepth 1000000 in
theorem work_keyFull : workAtMost 32 dKeyFull.ds₁ = true ∧ workAtMost 32 dKeyFull.ds₂ = true ∧
    workAtMost 32 dKeyFull.ds₃ = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem work_proofFull : workAtMost 32 dProofFull.ds₁ = true ∧
    workAtMost 32 dProofFull.ds₂ = true ∧ workAtMost 32 dProofFull.ds₃ = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem work_dsFull : (dsFull.all fun d => decide (d.entry.work ≤ 32)) = true := by decide +kernel

end Johnson.G

/-! ## 2. In general, at any data of rounds -/

namespace OnBytes.Prover
open _root_.Run
open OnBytes.Maker
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice
open OnBytes.K.Arm (length_sh)

section Frame
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)

/-- **The rounds of the three parts**, at any data of rounds: the lists' lengths; three more in a whole
file, one more in the link. -/
theorem rounds_of_data :
    ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).offline.shape.length +
      ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).link.shape.length +
      ((threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).withProvers P).onlineBatch.loc.shape.length =
    (DK.ds₁.length + DK.ds₂.length + DK.ds₃.length + 3) + (ds.length + 1) +
      (DP.ds₁.length + DP.ds₂.length + DP.ds₃.length + 3) := by
  have hT := length_sh (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty
  have hB := length_sh (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty
  have hL : (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec).shape.length = ds.length + 1 :=
    length_linkW _ _ _ _ _
  show (chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK) ByteArray.empty).sh.length +
      (linkProtocolOfRoundData (ckP .two) ds frS.P.T.a xs dec).shape.length +
      (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh.length = _
  rw [hL, hT, hB]
  show 1 + (DK.ds₁.length + (1 + (DK.ds₂.length + (1 + DK.ds₃.length)))) + (ds.length + 1) +
      (1 + (DP.ds₁.length + (1 + (DP.ds₂.length + (1 + DP.ds₃.length))))) = _
  omega

end Frame

end OnBytes.Prover

/-! ## 3. At every Z, from the data that are laid there -/

namespace AtPublicFiles.AtFiles
open Prob Hiop
open Iop (Strat Rho)
open OnBytes.Flat OnBytes.Maker OnBytes.Prover
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifierAndGoals (PublicFiles asDescriptionFiles InScope readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed key_built_written proof_built_written)
open Johnson.G

/-- **The largest work of a round at Z is at most n**, if no round's data has more: in the key file's
three lists, the link's list and the proof file's three lists. -/
theorem mostWorkAtFiles_le_of (Z : PublicFiles) {n : ℕ}
    (hK : ∀ d ∈ (dataAtFiles flashProveData Z).DK.ds₁ ++ ((dataAtFiles flashProveData Z).DK.ds₂ ++ (dataAtFiles flashProveData Z).DK.ds₃),
      d.entry.work ≤ n)
    (hL : ∀ d ∈ PV.EntryFive.dsF, d.entry.work ≤ n)
    (hP : ∀ d ∈ (dataAtFiles flashProveData Z).DP.ds₁ ++ ((dataAtFiles flashProveData Z).DP.ds₂ ++ (dataAtFiles flashProveData Z).DP.ds₃),
      d.entry.work ≤ n) : mostWorkAtFiles Z ≤ n :=
  max_le (mostWork_offlineWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK)
    (max_le (mostWork_linkWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL)
      (mostWork_onlineWires _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP))

/-- **The number of rounds of the whole run at Z**: the seven lists' lengths, and twelve. -/
theorem rounds_eq (Z : PublicFiles) (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill) :
    (((filesAt Z).withProvers P).wholeRunShape fill).length =
      ((dataAtFiles flashProveData Z).DK.ds₁.length + (dataAtFiles flashProveData Z).DK.ds₂.length +
          (dataAtFiles flashProveData Z).DK.ds₃.length + 3) + (PV.EntryFive.dsF.length + 1) +
        ((dataAtFiles flashProveData Z).DP.ds₁.length + (dataAtFiles flashProveData Z).DP.ds₂.length +
          (dataAtFiles flashProveData Z).DP.ds₃.length + 3) + 5 := by
  rw [Iop.HolographicProtocol.length_wholeRunShape]
  exact congrArg (· + 5) (rounds_of_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ P)

/-! ## 4. In scope, where protocolDataWellFormed says yes -/

/-- The key file's data that are laid there are the written lists, over the twin that the kernel
evaluates. -/
theorem keyDataInScope (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DK = dKeyFull :=
  (key_built_written Z scope live).trans writtenKFull_eq

/-- So are the proof file's. -/
theorem proofDataInScope (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (dataAtFiles flashProveData Z).DP = dProofFull :=
  (proof_built_written Z scope live).trans writtenPFull_eq

/-- **No round has more than 32 bits of proof of work.** -/
theorem mostWorkInScope (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    mostWorkAtFiles Z ≤ 32 :=
  mostWorkAtFiles_le_of Z
    (by rw [keyDataInScope Z scope live]; exact work_le_of_three work_keyFull)
    (by
      have h := work_dsFull
      simpa only [List.all_eq_true, decide_eq_true_eq] using h)
    (by rw [proofDataInScope Z scope live]; exact work_le_of_three work_proofFull)

/-- The link's written list has 41 rounds; the link, with the round in front, 42. -/
theorem linkRounds : PV.EntryFive.dsF.length + 1 = 42 :=
  (length_linkW _ _ _ _ _).symm.trans TypedOracleCompiler.Compile.Batch.Cms.sibF_len

/-- **The whole run has 67,391 rounds.** -/
theorem roundsInScope (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (P : (filesAt Z).Provers) (fill : ((filesAt Z).withProvers P).Fill) :
    (((filesAt Z).withProvers P).wholeRunShape fill).length = 67391 := by
  rw [rounds_eq, keyDataInScope Z scope live, proofDataInScope Z scope live,
    length_of_lenE len_keyFull.1, length_of_lenE len_keyFull.2.1, length_of_lenE len_keyFull.2.2,
    length_of_lenE len_proofFull.1, length_of_lenE len_proofFull.2.1,
    length_of_lenE len_proofFull.2.2, linkRounds]

/-- 2^w * 2^-128 ≤ 2^-96 where w ≤ 32. -/
theorem work32_times_bound {w : ℕ} (h : w ≤ 32) :
    ((2 ^ w : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ (2 : ℝ≥0∞)⁻¹ ^ 96 :=
  calc ((2 ^ w : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128
      ≤ ((2 ^ 32 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 :=
        mul_le_mul' (Nat.cast_le.2 (Nat.pow_le_pow_right (by decide) h)) le_rfl
    _ = (2 : ℝ≥0∞)⁻¹ ^ 96 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (128 : ℕ) = 32 + 96 from rfl, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- **THE BOUND**, at Z in scope, read, where protocolDataWellFormed says yes: for every P, every fill and every prover
of the whole run, over uniform points and the challenges that pass, the conclusion fails with
probability at most 67391 * 2^-96. -/
theorem probabilityInScope (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (P : (filesAt Z).Provers)
    (fill : ((filesAt Z).withProvers P).Fill) (β : Type)
    (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β) :
    pr (unif (Rho (((filesAt Z).withProvers P).wholeRunShape fill))) (ConclusionFails Z P fill prover) ≤
      (67391 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96 :=
  (probabilityAtFiles Z pp scope read live P fill β prover).trans
    (mul_le_mul' (le_of_eq (by rw [roundsInScope Z scope live P fill]; rfl))
      (work32_times_bound (mostWorkInScope Z scope live)))

/-- 67391 * 2^-96 ≤ 2^-79. -/
theorem bound_le_79 : (67391 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96 ≤ (2 : ℝ≥0∞)⁻¹ ^ 79 :=
  calc (67391 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96
      ≤ ((2 ^ 17 : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96 :=
        mul_le_mul' (by exact_mod_cast (by decide : (67391 : ℕ) ≤ 2 ^ 17)) le_rfl
    _ = (2 : ℝ≥0∞)⁻¹ ^ 79 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, show (96 : ℕ) = 17 + 79 from rfl, pow_add, ← mul_assoc,
          ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]

/-- The bound says something: it is below 1. -/
theorem bound_lt_one : (67391 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96 < 1 :=
  lt_of_le_of_lt (bound_le_79.trans (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 one_le_two)
    (by decide : 1 ≤ 79))) (by rw [pow_one]; exact ENNReal.inv_lt_one.2 (by norm_num))

/-- **The same, at most 2^-79.** -/
theorem probabilityInScope79 (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (read : readFiles Z = .ok pp) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (P : (filesAt Z).Provers)
    (fill : ((filesAt Z).withProvers P).Fill) (β : Type)
    (prover : Strat (((filesAt Z).withProvers P).wholeRunShape fill) β) :
    pr (unif (Rho (((filesAt Z).withProvers P).wholeRunShape fill))) (ConclusionFails Z P fill prover) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 79 :=
  (probabilityInScope Z pp scope read live P fill β prover).trans bound_le_79

end AtPublicFiles.AtFiles

#print axioms Johnson.G.work_keyFull
#print axioms Johnson.G.work_proofFull
#print axioms Johnson.G.work_dsFull
#print axioms OnBytes.Prover.rounds_of_data
#print axioms AtPublicFiles.AtFiles.mostWorkAtFiles_le_of
#print axioms AtPublicFiles.AtFiles.rounds_eq
#print axioms AtPublicFiles.AtFiles.keyDataInScope
#print axioms AtPublicFiles.AtFiles.proofDataInScope
#print axioms AtPublicFiles.AtFiles.mostWorkInScope
#print axioms AtPublicFiles.AtFiles.linkRounds
#print axioms AtPublicFiles.AtFiles.roundsInScope
#print axioms AtPublicFiles.AtFiles.probabilityInScope
#print axioms AtPublicFiles.AtFiles.bound_le_79
#print axioms AtPublicFiles.AtFiles.bound_lt_one
#print axioms AtPublicFiles.AtFiles.probabilityInScope79
