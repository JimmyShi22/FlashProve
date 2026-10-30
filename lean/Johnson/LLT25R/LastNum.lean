-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastNum.lean: THE LEDGER's FIELD `numbering` (LastLedger.lean) AT THE
NUMBERING OF A FILE's TREES (`numAt D.t₁ D.t₂ 2`, Johnson/Desc/BlockSlot.lean): ONE TEST ON
THE PLAN IS LEFT.
  `baseTwo_pure`: at the proof file's own description the third piece's base IS the last chain's
    first tree's number, `D.t₁ + D.t₂`: the two blocks in front of it declare no round, so they are
    cut no stretch and send no tree.
  `numbering_closed`: **`∀ n, numAt D.t₁ D.t₂ 2 (.own (π.nums.free + n)) = baseTwoAt … + n` FROM
    `π.nums.free = 0`**, π the place's numbers off the plan.
Limits. That free is 0 at the place is a comparison on the plan: evaluated nowhere here (in K12's
files' written-out places of the two stored sets the third place has free := 0:
Johnson/Desc/K12/Law/PlacesSmall.lean:160, PlacesFull.lean:202: read, not proved to be the planner's
values here). Nothing on soundness.
-/
import Johnson.LLT25R.LastSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) (D : WholeD)

/-- **The third piece's base is the last chain's first tree's number.** -/
theorem baseTwo_pure : baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N) = D.t₁ + D.t₂ := by
  show D.t₁ + D.t₂ + nTrees (D.ds₃.take 0) + nTrees ((D.ds₃.drop 0).take 0) = D.t₁ + D.t₂
  simp [nTrees]

/-- **The ledger's field `numbering`, from one comparison on the plan.** -/
theorem numbering_closed (hfree : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free = 0) (n : ℕ) :
    numAt D.t₁ D.t₂ 2 (.own ((H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.free + n)) =
      baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N) + n := by
  rw [baseTwo_pure, hfree]
  simp [numAt]

end LLT25

#print axioms LLT25.baseTwo_pure
#print axioms LLT25.numbering_closed
