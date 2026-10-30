-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/K12Members.lean: the three sampled members of the shared chain, as another file's list
writes them (Johnson/Desc/Sound/SharedMembers.lean: msSh S rU rO rSp …: the pairs (S.fold.u, rU),
(S.omega, rO), (S.sharedSplit, rSp)), ARE the pairs of K1's written records, at the typed shape of a
proof file and of a key file, with the three letters laid: a proof file: 8342416, 3131972, 6117; a
key file: 8342420, 3138896, 6130.
  members_are_real, members_are_key: the equation of the two lists: Lean's kernel
  fit_pairs_real, fit_pairs_key: so the comparison of Johnson/Goal/Numbers/K12Fit.lean holds at
      these three pairs, at both proximity tests, in the form of that list's own terms

What is not claimed. That a seated description's shape is the typed one. What the head of
K12Fit.lean does not claim. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K12Fit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open H2K.Member (setAt szUFull szOFull)
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)

/-- The three pairs in the order of the list msSh (Johnson/Desc/Sound/SharedMembers.lean). -/
def pairsOf (S : LinShape) (rU rO rSp : ℕ) : List (OracleShape × ℕ) :=
  [(S.fold.u, rU), (S.omega, rO), (S.sharedSplit, rSp)]

theorem members_are_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    membersOf 2 = pairsOf x.shape 8342416 3131972 6117 := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p =>
      decide (membersOf 2 = pairsOf p.1.shape 8342416 3131972 6117)) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, of_decide_eq_true h⟩

theorem members_are_key : membersOf 0 = pairsOf keyFull.once.shape 8342420 3138896 6130 := by
  decide +kernel

theorem fit_pairs_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    fitB setAt szUFull codesFull2 (pairsOf x.shape 8342416 3131972 6117) = true ∧
    fitB setAt szOFull codesFull2 (pairsOf x.shape 8342416 3131972 6117) = true := by
  obtain ⟨x, a1, a2⟩ := members_are_real
  exact ⟨x, a1, a2 ▸ fit_real_U, a2 ▸ fit_real_O⟩

theorem fit_pairs_key :
    fitB recordSet keyFull.once.folded.stages keyFull.codes
        (pairsOf keyFull.once.shape 8342420 3138896 6130) = true ∧
    fitB recordSet keyFull.once.omega.stages keyFull.codes
        (pairsOf keyFull.once.shape 8342420 3138896 6130) = true :=
  ⟨members_are_key ▸ fit_key_U, members_are_key ▸ fit_key_O⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.members_are_real
#print axioms Desc.K14.Law.members_are_key
#print axioms Desc.K14.Law.fit_pairs_real
#print axioms Desc.K14.Law.fit_pairs_key
