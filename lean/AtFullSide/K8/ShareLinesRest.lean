-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/ShareLinesRest.lean: two lines of the test on stated shares (E2E/TheFallsSum.lean):
the marks of the kinds K5 and K6 pass it, under the head.

  k5_marks_small   every mark of the attention segments' own rounds passes
  k6_marks_small   every mark of the output head's own rounds passes

Limits. A test on public numbers. It says nothing of what a mark's event costs.
-/
import E2E.TheFallsSum
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksSmall
import Johnson.Desc.ProofFile.Honest.K6.Law.K6MarksLaw

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open AtPublicFiles.TheFalls
open ProofFile.Honest (Mark Odds)
open ProofFile.Honest.K5 (k5Marks mkReads mkLive)
open VerifiableInference.Desc (KindName Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The pair of the kind K5's marks passes at a small number. -/
theorem pair_passes {k : ℕ} (hk : k ≤ 2 ^ 64) :
    shareSmall (⟨k * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * (2 ^ 128) ^ 3⟩ : Odds) = true := by
  have h₁ : 2 ^ 64 * (2 ^ 128 + 1) ^ 3 * 2 ^ 109 ≤ Code.pGold ^ 3 * (2 ^ 128) ^ 3 := by
    decide +kernel
  have h₀ : 0 < Code.pGold ^ 3 * (2 ^ 128) ^ 3 := by decide +kernel
  unfold shareSmall
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h₀, le_trans ?_ h₁⟩
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The marks of the kind K5 pass.** -/
theorem k5_marks_small (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (k5Marks Zp Bs.G₀).all markSmall = true := by
  refine List.all_eq_true.2 fun mk hm => ?_
  obtain ⟨b, hb, hp⟩ := ProofFile.Honest.K5.k5Marks_stands h hB mk hm
  obtain ⟨g, hg, a, ea, -, rfl | rfl⟩ :=
    ProofFile.Honest.K5.k5Marks_member_is_head h hB hm hb hp.symm
  · show (if (KindName.K5 = KindName.K3 ∨ KindName.K5 = KindName.K6) then _ else _) = true
    rw [if_neg (by decide)]
    exact pair_passes (le_trans (Nat.mul_le_mul_left 2 (ProofFile.Honest.K5.reads_length_head h hg ea))
      (by norm_num))
  · show (if (KindName.K5 = KindName.K3 ∨ KindName.K5 = KindName.K6) then _ else _) = true
    rw [if_neg (by decide)]
    refine pair_passes ?_
    rw [ProofFile.Honest.K5.live_length_head h hg ea]
    norm_num

/-- A number of named elements at the output head passes. -/
theorem head_passes {k : ℕ} (hk : k ≤ 100) : shareSmall ⟨k, fieldSize⟩ = true := by
  have h₁ : 100 * 2 ^ 109 ≤ fieldSize := by decide +kernel
  have h₀ : 0 < fieldSize := by decide +kernel
  unfold shareSmall
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h₀, le_trans (Nat.mul_le_mul_right _ hk) h₁⟩

/-- **The marks of the kind K6 pass.** -/
theorem k6_marks_small (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) :
    (ProofFile.Honest.K6.part4Marks Zp G₀).all markSmall = true := by
  obtain ⟨e₁, e₂⟩ := ProofFile.Honest.K6.part4Marks_rounds h hG
  have hg : ProofFile.Honest.K6.goodK6Events (ProofFile.Honest.K6.headParAt G₀) ≤ 100 := by
    have := ProofFile.Honest.K6.goodRounds_length (ProofFile.Honest.K6.headParAt G₀)
    omega
  show (markSmall _ && (markSmall _ && true)) = true
  simp only [Bool.and_true, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · show (if ((KindName.K6 = KindName.K3 ∨ KindName.K6 = KindName.K6)) then _ else _) = true
    rw [if_pos (Or.inr rfl)]
    exact head_passes hg
  · show (if ((KindName.K6 = KindName.K3 ∨ KindName.K6 = KindName.K6)) then _ else _) = true
    rw [if_pos (Or.inr rfl)]
    exact head_passes (by show 2 * _ ≤ 100; omega)

end AtFullSide.K8

#print axioms AtFullSide.K8.k5_marks_small
#print axioms AtFullSide.K8.k6_marks_small
