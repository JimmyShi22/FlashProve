-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/NoSideAtBase.lean: THE PROVER THAT THE MAKER `onlineProverFromPublicFiles` RETURNS AT THE FILLING `onlineProverPartsInUse`
(Honest/K1/Law/WSideAtFill.lean) HAS NO SIDE AT A PLACE OF THE KIND K9. The index I, its type, the hash function, the sizes
and the opening are variables; there is no premise but the maker's return.

Why. The filling's lots are ten lots whose sides stand at places of ten other kinds (`FirstFill.widerKinds`), the closings'
lot (kind K10: `closeLotAt_kinds`), the proximity test's (K12: `proxLotAt_kinds`) and the lot of one sending (one place,
of kind K1: `wLotAt_halves`). The maker's first list is these lots' sides in a row (`atPure_ok`).

  `lots_not_K9`         no side of a lot of that filling stands at a place of the kind K9
  **`no_side_at_base`**   so none of the returned prover's first list does
  **`find_none_at_base`**   so the search in that list at a place of the kind K9 finds none

Limits. Where the maker does not return nothing is said. The other two lists are not spoken of: no place of this kind
stands in their chains. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (KindName Place)

variable {W₀ : Type}

/-- No side of a lot of the filling stands at a place of the kind K9. -/
theorem lots_not_K9 (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Zq : Pub)
    (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots, ∀ g ∈ M.halves Zq G, g.place.kind ≠ KindName.K9 := by
  intro M hM g hg h9
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hk : q.2 = KindName.K9 := ((FirstFill.widerKinds I o S O Zq G).all q hq g hg).symm.trans h9
    have hin : KindName.K9 ∈ (widerPairs I o S O).map (·.2) := hk ▸ List.mem_map.2 ⟨q, hq, rfl⟩
    have hno : KindName.K9 ∉
        ([KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] : List KindName) := by decide
    exact hno hin
  · have hk := closeLotAt_kinds I S Zq G g hg
    rw [h9] at hk
    cases hk
  · have hk := proxLotAt_kinds I S Zq G g hg
    rw [h9] at hk
    cases hk
  · rw [wLotAt_halves] at hg
    obtain ⟨msg, _, rfl⟩ := Option.mem_toList.1 hg |> Option.mem_map.1
    cases h9

/-- **The returned prover has no side at a place of the kind K9.** -/
theorem no_side_at_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind ≠ KindName.K9 := by
  obtain ⟨-, -, -, -, -, -, -, hf, -⟩ := atPure_ok hA
  intro g hg
  rw [hf] at hg
  obtain ⟨M, hM, hx⟩ := List.mem_flatMap.1 hg
  exact lots_not_K9 I o S O A.Z A.G M hM g hx

/-- **The search at a place of the kind K9 finds none.** -/
theorem find_none_at_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) (q : Place) (hq : q.kind = KindName.K9) :
    (A.H.first.find? fun e => e.place == q) = none := by
  rw [List.find?_eq_none]
  intro e he hb
  have e1 : e.place = q := beq_iff_eq.1 hb
  exact no_side_at_base I o S O hA e he (e1 ▸ hq)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.lots_not_K9
#print axioms ProofFile.Honest.K9.no_side_at_base
#print axioms ProofFile.Honest.K9.find_none_at_base
