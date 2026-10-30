-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- where the kind K1 stands, and which rows are of that kind.
/-
Johnson/M1/K1Rows.lean: no sub-protocol of the last chain is of the kind K1, at a return of the maker,
so that chain's clause of `KindPays .K1` is empty. And at a list of lots in the filling's order whose
first is K1's own and last is W's, a row of the kind K1 is a row of one of these two: the premise `hk` of
`k1_first_pays`, given what the lots between them are. No property of the protocol is claimed here.
-/
import Johnson.M1.KindK1
import Johnson.M1.K1Only
import Johnson.M1.K1Order
import Johnson.M1.Ties
import Johnson.SendSim.Seat.AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutOf cutSecondFull)

variable {W₀ W₀' Rc' Pb Rc Tr X₀ X' : Type}

set_option maxRecDepth 1000000 in
/-- No row of the last chain's written cut is of the kind K1. -/
theorem second_written : (cutSecondFull.all fun r => r.2.1.kind != KindName.K1) = true := by
  decide +kernel

/-- **No sub-protocol of the last chain is of the kind K1**, at a return of the maker. -/
theorem second_no_k1 {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'} {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hS : VerifierAndGoals.InScope P = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R) :
    ∀ b ∈ R.F.second.blocksInOrder, b.place.kind ≠ KindName.K1 := by
  obtain ⟨Bs, base, c, A, B, O, -⟩ := open_of_return h
  obtain ⟨-, h4⟩ := OnBytes.SendSim.Seat.plan_of_live hL O
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨-, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  have e := (VerifiableInference.PlanWritten.cutIs_eq hc).2.2
  intro b hb hkd
  have hm : (b.name, b.place, b.rounds.length, b.oracles.length,
      VerifiableInference.PlanWritten.toldRounds b, b.before) ∈ cutSecondFull := by
    rw [← e]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  have h1 := List.all_eq_true.1 second_written _ hm
  simp only [bne_iff_ne, ne_eq] at h1
  exact h1 hkd

/-- **The last chain's clause of `KindPays .K1` is empty.** -/
theorem k1_last_empty {V W Y : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
    {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R)
    {L : Lettered R.B R.F.S₃ R.F.Cl V W Y Pb} (hk : L.place.kind = KindName.K1)
    {f : List (Fall R.F.S₃)} {σ : Side R.F.S₃ R.F.Cl V W Y Pb}
    (hσ : L.side R.F.second.blocksInOrder f = some σ) : False := by
  have hf := OnBytes.SendSim.Seat.find_of_seated hσ
  have hm := List.mem_of_find?_eq_some hf
  have hp := List.find?_some hf
  have e : σ.block.place = L.place := beq_iff_eq.1 hp
  exact second_no_k1 hS hL h _ hm (e ▸ hk)

/-- **No lot between them lays a half of the kind K1.** -/
theorem mid_no_k1 (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ midOf I o S O, ∀ g ∈ M.halves Z G, g.place.kind ≠ KindName.K1 := by
  intro M hM g hg e
  simp only [midOf, List.mem_append, List.mem_singleton] at hM
  rcases hM with (h | rfl) | rfl
  · have hnd := widerPairs_nodup (I := I) (o := o) (S := S) (O := O)
    have h2 : ∃ q ∈ (widerPairs I o S O).tail, q.1 = M := by
      have e2 : (widerFillAt I o S O).lots.tail = (widerPairs I o S O).tail.map (·.1) := rfl
      rw [e2] at h
      obtain ⟨q, hq, hq2⟩ := List.mem_map.1 h
      exact ⟨q, hq, hq2⟩
    obtain ⟨q, hq, rfl⟩ := h2
    have hq' : q ∈ widerPairs I o S O := List.mem_of_mem_tail hq
    have hk := (FirstFill.widerKinds I o S O Z G).all q hq' g hg
    rw [e] at hk
    have hno : KindName.K1 ∉ (widerPairs I o S O).tail.map (·.2) :=
      (List.nodup_cons.1 hnd).1
    exact hno (List.mem_map.2 ⟨q, hq, hk.symm⟩)
  · have hk := closeLotAt_kinds I S Z G g hg
    rw [e] at hk
    cases hk
  · have hk := proxLotAt_kinds I S Z G g hg
    rw [e] at hk
    cases hk

/-- **The premise `hk` of `k1_first_pays`**, at a list of lots that has K1's own first, W's last, and
between them lots that are `midOf` read through. -/
theorem rows_k1 (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (mid : List (SLot (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Unit Pb))
    (hm : mid.map SLot.toHLot =
      (midOf I o S O).map (HLot.thru (Local.thru g rd) (Local.thru g rd))) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) :
    ∀ r ∈ rowsOfLots Z G (k1Lot (Pb := Pb) I o S g rd :: (mid ++ [wLot (Pb := Pb) I o O g rd])),
      r.place.kind = KindName.K1 →
      r ∈ (k1Lot (Pb := Pb) I o S g rd).rows Z G ∨ r ∈ (wLot (Pb := Pb) I o O g rd).rows Z G := by
  intro r hr hk
  obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
  rcases List.mem_cons.1 hl with rfl | hl
  · exact .inl hrl
  rcases List.mem_append.1 hl with hl | hl
  · exfalso
    have h1 : l.toHLot ∈ (midOf I o S O).map (HLot.thru (Local.thru g rd) (Local.thru g rd)) := by
      rw [← hm]
      exact List.mem_map.2 ⟨l, hl, rfl⟩
    obtain ⟨M, hM, he⟩ := List.mem_map.1 h1
    have h2 : r.half ∈ (HLot.thru (Local.thru g rd) (Local.thru g rd) M).halves Z G := by
      rw [he]
      exact List.mem_map.2 ⟨r, hrl, rfl⟩
    obtain ⟨q, hq, hq2⟩ := List.mem_map.1 h2
    have hp : q.place = r.place := congrArg Placed.place hq2
    exact mid_no_k1 I o S O Z G M hM q hq (hp ▸ hk)
  · rcases List.mem_singleton.1 hl with rfl
    exact .inr hrl

end Johnson.M1

#print axioms Johnson.M1.k1_last_empty
#print axioms Johnson.M1.rows_k1
