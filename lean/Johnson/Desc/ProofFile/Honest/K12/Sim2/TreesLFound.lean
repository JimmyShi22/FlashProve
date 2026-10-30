-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the two sides of trees_first at the term's filling.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesLFound.lean: in the prover that onlineProverFromPublicFiles returns at the
filling read through (OnlineProverParts.through at onlineProverPartsInUse, which is what E2E's onlineFilling lays), the
search at a place of the code switch finds the half of the switch at the readers read through, and
the search at the first chain's last test finds the pair of the job read through. These are the
premises hgK and hg of trees_first and of the stand's laws, at the term.

  kindTwoLot       the kind K2's list in the filling
  lots_at_finish   every list of the filling has no half of the kind K2, or the kind K2's halves
  finish_found, finish_found_through   the search at a place of the code switch, at the filling and
                   read through
  last_test_found_through   the search at the first chain's last test

Limits. Conditional on onlineProverFromPublicFiles's return, and on the place being one of the kind's (hp). No property of
the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLThrough
import Johnson.Desc.ProofFile.Honest.K12.Sim2.FoundL
import Johnson.Desc.ProofFile.Honest.ThruK13
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile.Honest.FirstFill (ownPairs longKinds_plain k2_find_at k2_kind)

variable {W₀ W₀' Rc' : Type}

/-- The kind K2's list in the filling. -/
abbrev kindTwoLot (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
    K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩

/-- The readers of the filling, at a public part. -/
abbrev fillReaders (I : WiderIn W₀) (Z : Pub) : Local W₀ IndexCommitterCoins Inst Cells → Readers :=
  fun w => ⟨w.trace, I.weights Z w.w₀, w.rc⟩

/-- **Every list of the filling has no half of the kind K2, or the kind K2's halves.** -/
theorem lots_at_finish (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ x ∈ M.halves Z G, x.place.kind ≠ KindName.K2) ∨
        M.halves Z G = (kindTwoLot I S).halves Z G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · have hk := (longKinds_plain (X := Unit) I o S O Z G).all (S := S) (O := O)
    have h' : M ∈ (ownPairs (LongLots.plain o S O) I S O).map (·.1) := h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h'
    by_cases h2 : r.2 = KindName.K2
    · right
      simp only [ownPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | cases h2
    · exact .inl fun x hx e => h2 ((hk r hr x hx).symm.trans e)
  · refine .inl fun x hx e => ?_
    have hk := closeLotAt_kinds I S Z G x hx
    rw [e] at hk
    cases hk
  · refine .inl fun x hx e => ?_
    have hk := proxLotAt_kinds I S Z G x hx
    rw [e] at hk
    cases hk
  · refine .inl fun x hx e => ?_
    rw [wLot_place I o O Z G x hx] at e
    cases e

/-- **The search at a place of the code switch, at the filling.** -/
theorem finish_found {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces A.Z A.G) :
    A.H.first.find? (fun x => x.place == p.place) =
      some (K2.switchHalf (K2.coreSender K2.freshTable) (widerRows S A.Z A.G) (fillReaders I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) p) := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  obtain ⟨Z', Bs, base, c, A', B', Op⟩ := IM.seat_open hF
  obtain rfl : Z' = A.Z := Except.ok.inj (Op.pub.symm.trans hZ)
  have hkp : p.place.kind = KindName.K2 :=
    k2_kind (X := Unit) (widerRows S A.Z A.G) (fillReaders I A.Z) A.Z A.G _
      (List.mem_map.2 ⟨p, hp, rfl⟩)
  refine atPure_first_find_kind hA (L := kindTwoLot I S) ?_ (fun M hM => ?_)
    (k2_find_at (X := Unit) (widerRows S A.Z A.G) (fillReaders I A.Z) A.Z A.G Op hp)
  · rw [widerFillAtCPUOWM_lots]
    simp only [List.mem_append, List.mem_singleton]
    have hk : kindTwoLot I S ∈ (ownPairs (X := Unit) (LongLots.plain o S O) I S O).map (·.1) :=
      List.mem_map.2 ⟨_, .tail _ (.head _), rfl⟩
    exact .inl (.inl (.inl hk))
  · rcases lots_at_finish I o S O A.Z A.G M hM with h | h
    · exact .inl fun x hx e => h x hx (e.trans hkp)
    · exact .inr h

/-- **The search at a place of the code switch, at the filling read through.** -/
theorem finish_found_through {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces A.Z A.G) :
    A.H.first.find? (fun x => x.place == p.place) =
      some (K2.switchHalf (K2.coreSender K2.freshTable) (widerRows S A.Z A.G)
        (fillReaders I A.Z ∘ Local.thru g rd)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) p) := by
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  obtain ⟨Z', Bs, base, c, A', B', Op⟩ := IM.seat_open hF
  obtain rfl : Z' = A.Z := Except.ok.inj (Op.pub.symm.trans hZ)
  have hkp : p.place.kind = KindName.K2 :=
    k2_kind (X := Unit) (widerRows S A.Z A.G) (fillReaders I A.Z) A.Z A.G _
      (List.mem_map.2 ⟨p, hp, rfl⟩)
  refine atPure_first_find_kind hA (L := (kindTwoLot I S).thru (Local.thru g rd) (Local.thru g rd))
    (List.mem_map.2 ⟨_, ?_, rfl⟩) (fun M hM => ?_) ?_
  · rw [widerFillAtCPUOWM_lots]
    simp only [List.mem_append, List.mem_singleton]
    have hk : kindTwoLot I S ∈ (ownPairs (X := Unit) (LongLots.plain o S O) I S O).map (·.1) :=
      List.mem_map.2 ⟨_, .tail _ (.head _), rfl⟩
    exact .inl (.inl (.inl hk))
  · obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
    rcases lots_at_finish I o S O A.Z A.G M₀ hM₀ with h | h
    · refine .inl fun x hx e => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact h y hy (e.trans hkp)
    · refine .inr ?_
      show (M₀.halves A.Z A.G).map _ = ((kindTwoLot I S).halves A.Z A.G).map _
      rw [h]
  · show (((kindTwoLot I S).halves A.Z A.G).map _).find? _ = _
    rw [List.find?_map]
    have e := k2_find_at (X := Unit) (widerRows S A.Z A.G) (fillReaders I A.Z) A.Z A.G Op hp
    have e' : ((kindTwoLot I S).halves A.Z A.G).find?
        ((fun x => x.place == p.place) ∘ Placed.thru (Local.thru g rd) (Local.thru g rd)) =
        some (K2.switchHalf (K2.coreSender K2.freshTable) (widerRows S A.Z A.G) (fillReaders I A.Z)
          (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) p) := e
    rw [e']
    show some (Placed.thru _ _ _) = _
    rw [switchHalf_through]

/-- **The search at the first chain's last test, at the filling read through.** -/
theorem last_test_found_through {o' : SecondHashFunctionArgument} {pol lay KL : ByteArray} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (d' : W₀') {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)) = .ok A)
    (pl : K2.SwitchPlace) (hf : finishAt A.Z A.G = some pl)
    (hfit : fitsL (H2U.p12OfMade A.Z.made) pl = true) :
    A.H.first.find? (fun x => x.place == placeL) =
      some (proverSideOfProximityTest ((jobAtLastTest I S A.Z A.G pl).through (Local.thru g rd))) := by
  refine atPure_first_find hA (L := (proxLotAt I S).thru (Local.thru g rd) (Local.thru g rd))
    (List.mem_map.2 ⟨_, proximity_lot_mem I o S O, rfl⟩) (fun M hM => ?_) ?_
  · obtain ⟨M₀, hM₀, rfl⟩ := List.mem_map.1 hM
    rcases lots_at_last_test I o S O A.Z A.G M₀ hM₀ with h | h
    · refine .inl fun x hx e => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      exact h y hy e
    · refine .inr ?_
      show (M₀.halves A.Z A.G).map _ = ((proxLotAt I S).halves A.Z A.G).map _
      rw [h]
  · show (((proxLotAt I S).halves A.Z A.G).map _).find? _ = _
    obtain ⟨c, hc⟩ := atPure_prox_arm hA
    rw [proxLotAt_made I S A.G hc]
    have e : (proxLotOf (X := Unit) I S).halves A.Z A.G =
        [proverSideOfProximityTest (jobAtLastTest I S A.Z A.G pl)] :=
      halves_lotAtDoor (widerRows S) (fun Z _ (w : Local W₀ IndexCommitterCoins Inst Cells) =>
        ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
        (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) A.Z A.G pl hf hfit
    rw [e]
    show List.find? _ [Placed.thru _ _ (proverSideOfProximityTest (jobAtLastTest I S A.Z A.G pl))] = _
    rw [testHalf_through]
    refine List.find?_cons_of_pos ?_
    show ((H2U.p12OfMade A.Z.made).place == placeL) = true
    rw [proxPlace]
    exact beq_self_eq_true _

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.lots_at_finish
#print axioms ProofFile.Honest.K12.Sim2.finish_found
#print axioms ProofFile.Honest.K12.Sim2.finish_found_through
#print axioms ProofFile.Honest.K12.Sim2.last_test_found_through
