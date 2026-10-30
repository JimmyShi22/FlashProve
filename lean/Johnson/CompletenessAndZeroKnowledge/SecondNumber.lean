-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/SecondNumber.lean: THE INDEX-PRIVACY ERROR AT THE SETTINGS, BUT FOR THE STOPS. At theSettings with
the chosen search limits, at public files in scope where protocolDataWellFormed says yes, at every value of the public
reading and for any provers: at most 2^64 + 1 queries and 688,127 requests, indexPrivacyError is at most
2^-157 plus the measures of the private stops (Budget's three fields). One copy; a leaf's salt has 320 free bits. The stops are the
provers' numbers. Nothing here is claimed of a protocol: this file proves neither completeness nor
zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.FirstNumber
import Johnson.CompletenessAndZeroKnowledge.ZetaAtTarget
import Johnson.CompletenessAndZeroKnowledge.PublicAtFlash

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace FlashProve
open Johnson.G (writtenKFull writtenPFull)
open OnBytes.Prover

theorem capAt_le_40 (work : ℕ → ℕ) (h : ∀ j, work j ≤ 32) (j : ℕ) : capAt work j ≤ 2 ^ 40 := by
  unfold capAt
  have h1 : 2 ^ (work j + 6) ≤ 2 ^ 38 := Nat.pow_le_pow_right (by norm_num) (by have := h j; omega)
  have h2 : (2 : ℕ) ^ 38 ≤ 2 ^ 40 := by norm_num
  omega

variable {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk)

theorem capT_le (eK : S.DK = writtenKFull) (j : ℕ) : capT S j ≤ 2 ^ 40 :=
  capAt_le_40 _ (workAt_le (S.DK.at OnBytes.Slice.frS.P.T.a) (tested_key S.DK eK).2.1 (tested_key S.DK eK).2.2.1
    (tested_key S.DK eK).2.2.2) j

theorem capB_le (eP : S.DP = writtenPFull) (j : ℕ) : capB S j ≤ 2 ^ 40 :=
  capAt_le_40 _ (workAt_le (S.DP.at OnBytes.Slice.frS.P.T.a) (tested_proof S.DP eP).2.1
    (tested_proof S.DP eP).2.2.1 (tested_proof S.DP eP).2.2.2) j

theorem capL_le (j : ℕ) : capL j ≤ 2 ^ 40 :=
  capAt_le_40 _ (fun k => by
    unfold workL
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      rw [List.getD_cons_succ]
      rcases Nat.lt_or_ge k (PV.EntryFive.dsF.map (·.entry.work)).length with h | h
      · rw [List.getD_eq_getElem _ _ h]
        exact le32_of work_copy _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]
        exact Nat.zero_le _) j

end FlashProve

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve
open OnBytes.Prover OnBytes.WholeKey OnBytes.FrontRoad AtPublicFiles.ZetaAt.Target
open IntegerTransformer (Settings)

/-- **THE SECOND NUMBER, BUT FOR THE STOPS.** -/
theorem indexPrivacyError_theSettings (files : PublicFiles) (settings : Settings)
    (fallbackInstance : (flashProveDescription.C files).X) (provers : HonestProvers (FlashProtocol files))
    (starts : SaltStarts provers) (slotSalts : RequestLeafSaltLayout) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) (N : Budget) (sessionsPerCopy t n : ℕ)
    (reading : FlashReading files) (ht : t ≤ 2 ^ 64 + 1) (hn : n ≤ sessionsPerCopy)
    (hn' : n ≤ 688127) :
    indexPrivacyError (flashLayout files settings fallbackInstance reading) provers
        (theSettings files settings fallbackInstance provers starts (writtenLimits files) slotSalts
          reading) N sessionsPerCopy t n ≤
      (2⁻¹ : ℝ≥0∞) ^ 157 + (N.offlineStops + N.linkStops + (n : ℝ≥0∞) * N.onlineStops) := by
  have hF : Fine ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).at reading) :=
    flash_at_of_all files Fine (fun c m => fine_atFiles files scope live c m) reading
  have eK := key_built_written files scope live
  have eP := proof_built_written files scope live
  refine (zeta_target_304 ((layoutsOfBuiltDescription flashProveData allZeroDigest [] files).at reading) hF
    (honestSide (flashLayout files settings fallbackInstance reading) provers
      (theSettings files settings fallbackInstance provers starts (writtenLimits files) slotSalts
        reading))
    (theSettings files settings fallbackInstance provers starts (writtenLimits files) slotSalts
      reading).coinNumbers (numbersOf N sessionsPerCopy) t n rfl ht hn hn'
    (capT_le (dataAtFiles flashProveData files) eK) capL_le (capB_le (dataAtFiles flashProveData files) eP)
    (by show 304 ≤ 320; norm_num)).trans (le_of_eq ?_)
  congr 1
  show ((0 : ℝ≥0∞) + (((0 + 1 : ℕ) : ℝ≥0∞)) * 0 + (n : ℝ≥0∞) * 0) +
      (N.offlineStops + (((0 + 1 : ℕ) : ℝ≥0∞)) * N.linkStops + (n : ℝ≥0∞) * N.onlineStops) +
      (((0 + 2 : ℕ) : ℝ≥0∞)) * 0 = _
  simp

end VerifiableInference.Compilation

#print axioms FlashProve.capT_le
#print axioms VerifiableInference.Compilation.indexPrivacyError_theSettings
