-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/FrameInScope.lean: the code switch: at public files in the goals' scope,
where the proof file's value is laid (`LPFD.Full.proofDataAndDecisionOfPublicFiles`, Johnson/Desc/Laid/ProofFull.lean), with
the data D: three facts on the frame that the rule of composition has for the first chain,
⟨a, allOf (D.at a), (D.at a).key₁, 0⟩. Statements and proofs; no definition.

  `t₁_written`      the first chain of the written data of the full size sends 83 trees: the
                    closed fact `Johnson.G.t1_proofFull`, at `writtenPFull`
  `t₁_in_scope`     so D.t₁ = 83
  `first_in_scope`  the field "first" of the switch's premise on the keys (ColsAtStageFirst.lean's
                    hFirst), at every base ≤ 83
  `low_in_scope`    a number below a base ≤ 83 is below 2 ^ 16
Limits. That a place's base is at most 83, and that the trees which a switch reads have numbers
below its base, is not said here. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.KeyOfData
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (allOf nAll)
open Johnson.G (writtenPFull writtenPFull_eq t1_proofFull)
open LPFD.Full (proofDataAndDecisionOfPublicFiles laidPOf_ok laidPOf_written RunPF)

theorem t₁_written : writtenPFull.t₁ = 83 := by
  rw [writtenPFull_eq]
  exact t1_proofFull

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : RunPF}

/-- **In scope the first chain sends 83 trees.** -/
theorem t₁_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) : D.t₁ = 83 := by
  rw [laidPOf_written hZ h]
  exact t₁_written

/-- **"first" at the frame, in scope.** -/
theorem first_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) (a' a base : Nat) (ds : List RDT)
    (hb : base ≤ 83) :
    ∀ j, j < (⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).base →
      ((⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).Lin.find? fun L =>
        (⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).key L.no ==
          (⟨a, base, allOf (D.at a'), ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).key j).map
            (·.no) = some j := by
  obtain ⟨F, -, -, hD, -, -⟩ := laidPOf_ok h
  exact first_of_data_at hD a' a base ds (by rw [t₁_in_scope hZ h]; exact hb)

theorem low_in_scope {base x : Nat} (hb : base ≤ 83) (hx : x < base) : x < 2 ^ 16 := by
  have : (83 : Nat) < 2 ^ 16 := by decide
  omega

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.t₁_written
#print axioms VerifiableInference.Desc.First.K2.t₁_in_scope
#print axioms VerifiableInference.Desc.First.K2.first_in_scope
#print axioms VerifiableInference.Desc.First.K2.low_in_scope
