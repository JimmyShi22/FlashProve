-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/Crossing.lean: the proof of K11HalfThrough (E2E/K11Crossing.lean), and the premise on
the cells at the online prover's index.

  headMergeHalf_thru     the kind's side at a reader composed with a total map is the side read
                         through that map
  k11_hex_through, k11_ho_through   the two premises on the lots, at a filling read through
  k11HalfThrough         the statement
-/
import E2E.K11Crossing
import AtFullSide.K11.AtTheTerm
import AtFullSide.K11.MatrixAtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain Place KindName)
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile (SecondHashFunctionArgument Pub Ground Inst)
open ProofFile.Honest
open ProofFile.Honest.K11
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open AtPublicFiles.AtFiles.HonestTerm.K11Term
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull placeOfLot)

section Thru
variable {W₀ W₀' Rc Rc' Xi Tr X : Type}

/-- **The kind's side at a reader composed with a total map is the side read through that map.** -/
theorem headMergeHalf_thru (g : W₀' → W₀) (rd : Rc' → Rc)
    (claims : Xi → List Fmt.Drawn → List WsClaim) (wt : W₀ → Weights) (P : HeadMergeP) :
    (headMergeHalf claims (wt ∘ g) P : Placed (Local W₀' Rc' Xi Tr) (Local W₀' Rc' Xi Tr) X) =
      (headMergeHalf claims wt P : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).thru
        (Local.thru g rd) (Local.thru g rd) := by
  unfold headMergeHalf headMergeRow headMergeDraw headMergeSum Placed.thru
  simp only [List.map_cons, List.map_nil]
  rw [quietPart_thru, Part.lift_thru]
  rfl

end Thru

section Lots
variable {W₀ Rc' : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : Sz)
  (O : OnlineProverArguments) (rd : Rc' → IndexCommitterCoins) (d : W₀) (Zq : Pub) (G : Ground)

/-- What the kind's lot holds, read through. -/
theorem k11_byPub_through :
    ((HLot.byPub I.weights (LongLots.plain o S O).k11 :
        HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).thru
      (Local.thru id rd) (Local.thru id rd)).halves Zq G =
      (headMergeLot O.claims (I.weights Zq)).halves Zq G :=
  congrArg (fun h => [h]) (headMergeHalf_thru id rd _ _ _).symm

/-- **Some lot of the filling read through has the kind's halves.** -/
theorem k11_hex_through :
    ∃ M ∈ (OnlineProverParts.through id rd d (onlineProverPartsInUse I o S O)).lots, M.halves Zq G =
      (headMergeLot O.claims (I.weights Zq)).halves Zq G :=
  ⟨(HLot.byPub I.weights (LongLots.plain o S O).k11 :
      HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).thru
    (Local.thru id rd) (Local.thru id rd),
    List.mem_map.2 ⟨_, k11_mem_wM I o S O, rfl⟩, k11_byPub_through I o S O rd Zq G⟩

/-- **Every lot of the filling read through has no half at a place of the kind, or the kind's
halves.** -/
theorem k11_ho_through :
    ∀ M ∈ (OnlineProverParts.through id rd d (onlineProverPartsInUse I o S O)).lots,
      (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K11) ∨
        M.halves Zq G = (headMergeLot O.claims (I.weights Zq)).halves Zq G := by
  intro M hM
  have hM' : M ∈ (onlineProverPartsInUse I o S O).lots.map
      (HLot.thru (Local.thru id rd) (Local.thru id rd)) := hM
  obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM'
  rcases k11_ho I o S O Zq G M₀ hM₀ with hk | he
  · refine .inl fun x hx e => ?_
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact hk y hy e
  · refine .inr ?_
    show (M₀.halves Zq G).map (Placed.thru (Local.thru id rd) (Local.thru id rd)) = _
    rw [he]
    exact congrArg (fun h => [h]) (headMergeHalf_thru id rd _ _ _).symm

end Lots

/-- **The side at the kind's place of the online prover's return is the base side read through.** -/
theorem k11HalfThrough : K11HalfThrough := by
  intro Z D r Zp Np cF x A Bs hM h hB
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  obtain ⟨Bs', base, Op⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (Op.made.symm.trans hB)
  have hG : A.G = Bs'.G₀ := Option.some.inj ((atPure_ok hM).2.1.symm.trans Op.blank)
  have hex := k11_hex_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z)
    matrixInput.dummy A.Z A.G
  have ho := k11_ho_through matrixInput OnBytes.secondHashFunction Sz.ref openHonest (tableCoins Z)
    matrixInput.dummy A.Z A.G
  have hh := (halfAtAnyFillHead Z D r _ Np cF x h _ _ _ _ _ (onlineFilling Z) A Bs' headClaimsByPlace
    (matrixInput.weights A.Z) hB hM hex ho).2.2
  refine ⟨?_, fun M hM' => ?_⟩
  · rw [hh]
    exact congrArg some (headMergeHalf_thru id (tableCoins Z) _ _ _)
  · rcases ho M hM' with hk | he
    · exact .inl hk
    · refine .inr ?_
      rw [he, hG]
      exact congrArg (fun g => [g]) (headMergeHalf_thru id (tableCoins Z) _ _ _)

end AtFullSide.K11

#print axioms AtFullSide.K11.headMergeHalf_thru
#print axioms AtFullSide.K11.k11_hex_through
#print axioms AtFullSide.K11.k11_ho_through
#print axioms AtFullSide.K11.k11HalfThrough
