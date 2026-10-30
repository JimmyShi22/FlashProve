-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/OwnKeyBook.lean: row 16's tests on the book, at the key's book, by
Lean's kernel: the entries that the own test's second part carries: number 0 is the index sender's
message, 1 and 3 W's two messages, 2 Omega's; and Omega's sender has no row of the first chain.

  own_book_full   the five at the written key
  own_book_at     at any plans with those codes and messages

Limits: the written key. No property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFoldedPub
import E2E.KeyJobW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub rideW ownTestPlace idxPlace wPlace omegaPlace omegaTestPlace)
open AtPublicFiles.KeyLay (parIK parWK AK)

set_option maxHeartbeats 0 in
theorem own_book_full : (fullPub.map fun K =>
    k1CutFits (keyBook K) ⟨ownTestPlace, 1⟩ 0 ⟨idxPlace, 0⟩ parIK (fun _ => none)
        (parIK.sent.size - 1) &&
      k1CutFits (keyBook K) ⟨ownTestPlace, 1⟩ 1 ⟨wPlace, 0⟩ parWK rideW 0 &&
      k1CutFits (keyBook K) ⟨ownTestPlace, 1⟩ 3 ⟨wPlace, 0⟩ parWK rideW 1 &&
      Light.cutFits (keyBook K) ⟨ownTestPlace, 1⟩ 2 ⟨omegaPlace, 0⟩ (K14.jobOmega AK) 0 &&
      (keyBook K).first.all fun r => r.1 != (⟨omegaPlace, 0⟩ : Addr)) = some true := by
  decide +kernel

theorem cutFits_plan (Bk : ProverCoinCounts) (a s : Addr) (n k : ℕ) (A : K14.SendPub) :
    Light.cutFits Bk a n s (K14.jobOmega A) k =
      Light.cutFits Bk a n s (K14.jobOmega (Light.planOf A.P.codes A.P.S)) k := rfl

set_option maxHeartbeats 0 in
/-- The cuts at the test on Omega, at the key's book, at the written plan. -/
theorem omega_book_full : (fullPub.map fun K => Light.bookCutsOmega (keyBook K) planK
    H2K.Member.piKOFull) = some true := by
  decide +kernel

/-- **Row 16's tests on the book, at plans by their codes and messages.** -/
theorem own_book_at {K : KeyPub} (hK : fullPub = some K) {PI PW : VerifiableInference.Desc.K1.Par}
    (hIc : PI.codes = parIK.codes) (hIs : PI.sent = parIK.sent)
    (hWc : PW.codes = parWK.codes) (hWs : PW.sent = parWK.sent) (A : K14.SendPub)
    (hAc : A.P.codes = AK.P.codes) (hAS : A.P.S = AK.P.S) :
    k1CutFits (keyBook K) ⟨ownTestPlace, 1⟩ 0 ⟨idxPlace, 0⟩ PI (fun _ => none)
        (parIK.sent.size - 1) = true ∧
      k1CutFits (keyBook K) ⟨ownTestPlace, 1⟩ 1 ⟨wPlace, 0⟩ PW rideW 0 = true ∧
      k1CutFits (keyBook K) ⟨ownTestPlace, 1⟩ 3 ⟨wPlace, 0⟩ PW rideW 1 = true ∧
      Light.cutFits (keyBook K) ⟨ownTestPlace, 1⟩ 2 ⟨omegaPlace, 0⟩ (K14.jobOmega A) 0 = true ∧
      ∀ r ∈ (keyBook K).first, r.1 ≠ (⟨omegaPlace, 0⟩ : Addr) := by
  have e := own_book_full
  rw [hK] at e
  have e' := Option.some.inj e
  simp only [Bool.and_eq_true] at e'
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := e'
  refine ⟨(k1CutFits_congr _ _ _ _ hIc hIs _ _).trans h1, (k1CutFits_congr _ _ _ _ hWc hWs _ _).trans h2,
    (k1CutFits_congr _ _ _ _ hWc hWs _ _).trans h3, ?_, fun r hr => ?_⟩
  · rw [cutFits_plan, hAc, hAS, ← cutFits_plan]
    exact h4
  · have := List.all_eq_true.1 h5 r hr
    simpa using this

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.own_book_full
#print axioms ProofFile.Honest.K12.Sim2.own_book_at
#print axioms ProofFile.Honest.K12.Sim2.omega_book_full
