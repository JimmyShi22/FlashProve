-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/FillPairs.lean: the thirteen lots of the filling
`onlineProverPartsInUse` (Honest/K1/Law/WSideAtFill.lean), each with its kind. Stated at the filling
itself, with the index's type and the value `I` as letters, before anything is read through. One
definition; eight theorems.

  `fillPairs`         the thirteen, in the filling's order
  `fillPairs_lots`    they are the filling's lots
  `fillPairs_kinds`   each lot lays sides of its own kind alone
  `lot_alone`         where the only pair of kind κ holds L, no other lot lays a side of that kind
  `lot_of_kind`       a side of kind κ lies in a lot whose pair is of kind κ
  `pair_only`         a pair among the first ten, of a kind other than K1, is the only one of its kind
  `close_pair_only`, `prox_pair_only`   the like for K10 and K12
  `k1_pairs`          K1's two lots

Limits.
  * Of a side the statements on kinds read its place alone.
  * K1 has two pairs: its own lot and the lot of the message W. `lot_alone` does not apply to it.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import AtFullSide.K12.ReturnsAtFillW

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest
open VerifiableInference.Desc (Block KindName)

section
variable {W₀ : Type}

/-- **The thirteen lots of the base filling, each with its kind.** -/
def fillPairs (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    List (HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit × KindName) :=
  widerPairs I o S O ++
    [(closeLotAt I S, .K10), (proxLotAt I S, .K12), (wLotAt I o O, .K1)]

/-- They are the filling's lots. -/
theorem fillPairs_lots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    (onlineProverPartsInUse I o S O).lots = (fillPairs I o S O).map (·.1) := rfl

/-- **Each lot lays sides of its kind alone.** No premise. -/
theorem fillPairs_kinds (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) :
    ∀ r ∈ fillPairs I o S O, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2 := by
  intro r hr x hx
  rcases List.mem_append.1 hr with h | h
  · exact (FirstFill.widerKinds I o S O Z G).all r h x hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact closeLotAt_kinds I S Z G x hx
    · exact proxLotAt_kinds I S Z G x hx
    · rw [AtFullSide.K12.wHalf_place I o O Z G x hx]

/-- **A side of kind κ lies in a lot whose pair is of kind κ.** -/
theorem lot_of_kind (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {κ : KindName} (Z : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots, ∀ x ∈ M.halves Z G, x.place.kind = κ →
      (M, κ) ∈ fillPairs I o S O := by
  intro M hM x hx hk
  rw [fillPairs_lots] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  have e := (fillPairs_kinds I o S O Z G r hr x hx).symm.trans hk
  subst e
  exact hr

/-- **Where the only pair of kind κ holds L, no other lot lays a side of that kind.** -/
theorem lot_alone (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {κ : KindName} {L : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit}
    (hu : ∀ M, (M, κ) ∈ fillPairs I o S O → M = L) (Z : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots, M = L ∨ ∀ x ∈ M.halves Z G, x.place.kind ≠ κ := by
  intro M hM
  rw [fillPairs_lots] at hM
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM
  by_cases e : r.2 = κ
  · subst e
    exact Or.inl (hu r.1 hr)
  · exact Or.inr fun x hx hk => e ((fillPairs_kinds I o S O Z G r hr x hx).symm.trans hk)

/-- **A pair among the first ten, of a kind other than K1, is the only one of its kind.** -/
theorem pair_only (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {κ : KindName} {L : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit}
    (hL : (L, κ) ∈ widerPairs I o S O) (hκ : κ ≠ .K1) :
    ∀ M, (M, κ) ∈ fillPairs I o S O → M = L := by
  intro M hM
  rcases List.mem_append.1 hM with h | h
  · exact congrArg Prod.fst (List.inj_on_of_nodup_map widerPairs_nodup h hL rfl)
  · have hk : κ ∈ (widerPairs I o S O).map (·.2) := List.mem_map.2 ⟨_, hL, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact absurd hk (by simp [widerPairs])
    · exact absurd hk (by simp [widerPairs])
    · exact absurd rfl hκ

/-- **The closings' lot is the only one of the kind K10.** -/
theorem close_pair_only (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ M, (M, KindName.K10) ∈ fillPairs I o S O → M = closeLotAt I S := by
  intro M hM
  rcases List.mem_append.1 hM with h | h
  · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩ : KindName.K10 ∈ (widerPairs I o S O).map (·.2))
      (by simp [widerPairs])
  · simpa using h

/-- **The proximity tests' lot is the only one of the kind K12.** -/
theorem prox_pair_only (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ M, (M, KindName.K12) ∈ fillPairs I o S O → M = proxLotAt I S := by
  intro M hM
  rcases List.mem_append.1 hM with h | h
  · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩ : KindName.K12 ∈ (widerPairs I o S O).map (·.2))
      (by simp [widerPairs])
  · simpa using h

/-- **K1's two lots.** -/
theorem k1_pairs (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ M, (M, KindName.K1) ∈ fillPairs I o S O →
      M ∈ [HLot.byPub I.weights (LongLots.plain o S O).k1, wLotAt I o O] := by
  intro M hM
  rcases List.mem_append.1 hM with h | h
  · exact List.mem_cons.2 (Or.inl (congrArg Prod.fst
      (List.inj_on_of_nodup_map widerPairs_nodup h (List.Mem.head _) rfl)))
  · exact List.mem_cons.2 (Or.inr (List.mem_singleton.2 (by simpa using h)))

end

end ProofFile.Honest

#print axioms ProofFile.Honest.fillPairs
#print axioms ProofFile.Honest.fillPairs_lots
#print axioms ProofFile.Honest.fillPairs_kinds
#print axioms ProofFile.Honest.lot_of_kind
#print axioms ProofFile.Honest.lot_alone
#print axioms ProofFile.Honest.pair_only
#print axioms ProofFile.Honest.close_pair_only
#print axioms ProofFile.Honest.prox_pair_only
#print axioms ProofFile.Honest.k1_pairs
