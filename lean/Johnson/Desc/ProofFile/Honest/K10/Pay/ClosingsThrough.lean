-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/ClosingsThrough.lean: the closing of a segment (K10): at the prover that the maker
`onlineProverFromPublicFiles` returns at the filling `onlineProverPartsInUse` read through two maps, the first half at each closing's place is the
closing's own.

The filling is `OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)`: thirteen lots (the ten of
`widerFillAt`, the closings', the proximity tests', the message W's), each read through the maps g (of the index) and rd
(of the stored tables' randomness). `ClosingsFirst` (Honest/K10/Thr/HalfOfLot.lean) is the premise on the prover's list
of halves that the laws on the closing's play and acceptance take.

  `thru_kind`           reading a lot through keeps its halves' places
  **`closingsFirst_through`**   where `onlineProverFromPublicFiles` returns A at that filling: the returned description opens at some first
                      chain c, and `ClosingsFirst` holds of A's list for the first chain, at the inner filling's readers
                      composed with the map of inputs, its rows' data, and the filler `stAtZero` at c's flat list

Limits. That `onlineProverFromPublicFiles` returns is a premise. The statement names the first half's parts alone; what they send is not read.
Where the public part has no closing (`closePars` is empty) it holds for nothing. No file here ties this filling to a named
prover of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AcceptedAtBase
import Johnson.Desc.ProofFile.Honest.K10.Pay.ThroughClose
import Johnson.Desc.ProofFile.Honest.AtPureWiderK10Kinds
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.ThruK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (KindName)

variable {W₀ W₀' Rc' X : Type}

/-- Reading a lot through keeps its halves' places: a property of all places of its halves is kept. -/
theorem thru_kind {V V' W W' : Type} (see : V' → V) (wit : W' → W) (M : HLot V W X) (Z : Pub) (G : Ground)
    (h : ∀ e ∈ M.halves Z G, e.place.kind ≠ KindName.K10) :
    ∀ e ∈ (M.thru see wit).halves Z G, e.place.kind ≠ KindName.K10 := by
  intro e he
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 (show e ∈ (M.halves Z G).map (Placed.thru see wit) from he)
  exact h e' he'

/-- **At the filling read through each closing's place is served by the closing's own half.** -/
theorem closingsFirst_through (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀') (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A) :
    ∃ Bs base c Sh Se, IM.Open o' pol lay KL A.F A.Z Bs base c Sh Se ∧
      ClosingsFirst A.H.first
        ((fun w : Local W₀ IndexCommitterCoins Inst Cells => (⟨w.trace, I.weights A.Z w.w₀, w.rc⟩ : Readers)) ∘ Local.thru g rd)
        (widerRows S A.Z A.G) (stAtZero c.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.Z A.G := by
  obtain ⟨Bs, base, c, Sh, Se, Op⟩ := atPure_open hA
  have hc := closeLotAt_of_open (X := Unit) I S A.G Op
  refine ⟨Bs, base, c, Sh, Se, Op, ?_⟩
  have hlots : (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots =
      ((((widerFillAt I o S O).lots ++ [closeLotAt I S]) ++ [proxLotAt I S]) ++ [wLotAt I o O]).map
        (HLot.thru (Local.thru g rd) (Local.thru g rd)) := by
    rw [← widerFillAtCPUOWM_lots]
    rfl
  refine closingsFirst_of_fill hA _ _ _
    (Lc := (closeLotAt I S).thru (Local.thru g rd) (Local.thru g rd)) ?_ ?_ ?_
  · rw [hlots]
    refine List.mem_map.2 ⟨closeLotAt I S, ?_, rfl⟩
    simp
  · rw [← seatLotC_through]
    show ((closeLotAt I S).halves A.Z A.G).map _ = ((seatLotC _ _ _).halves A.Z A.G).map _
    rw [hc]
  · intro M hM
    rw [hlots] at hM
    obtain ⟨M', hM', rfl⟩ := List.mem_map.1 hM
    simp only [List.mem_append, List.mem_singleton] at hM'
    rcases hM' with ((h | rfl) | rfl) | rfl
    · exact .inl (thru_kind _ _ M' A.Z A.G (ten_not_K10_plain I o S O A.Z A.G M' h))
    · exact .inr rfl
    · refine .inl (thru_kind _ _ _ A.Z A.G fun e he hk => ?_)
      have hk' := proxLotAt_kinds I S A.Z A.G e he
      rw [hk] at hk'
      cases hk'
    · exact .inl (thru_kind _ _ _ A.Z A.G (wLotAt_not_K10 I o O A.Z A.G))

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.thru_kind
#print axioms ProofFile.Honest.K10.closingsFirst_through
