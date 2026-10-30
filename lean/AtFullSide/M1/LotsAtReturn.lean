-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsAtReturn.lean: the rule's door at a return of the maker, in the goals' scope where
the gate accepts: the book is the written entries, the order is the written description's, and every
spending entry of a lots' sender passes lotsOkB at the return's own public part, ground, book and order.

  ahead_at_ret      R.B.ahead = rawAheadW and orderOf R.F = orderOf WP
  door_at_return    the door, from the three kernel facts

No fact on what a run shows: the book's entries and the tests on them.
-/
import AtFullSide.M1.LotsDoor
import AtFullSide.K14.BookWholeWritten
import Johnson.M1.Goal
import Johnson.Desc.ProofFile.Honest.AtPureBook
import Johnson.Desc.ProofFile.Honest.BookWholeAlike
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 AtFullSide.K14
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc (PlanAlike)
open VerifiableInference.Desc.K1 (qFull firstPar parW)
open VerifiableInference.Desc.K13.Law (gpFull wMsgFull)

variable {W₀ Rc Tr X₀ X' : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr X₀ X'}
  {R : OnlineProverWithDescription W₀ Rc Tr X₀ X'}

theorem ahead_at_ret (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R) :
    R.B.ahead = rawAheadW ∧ orderOf R.F = orderOf WP := by
  obtain ⟨Bs, base, c, A, B, O, hG⟩ := Johnson.M1.open_of_return h
  obtain ⟨h2, h4⟩ := plan_of_live hL O
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := R.Z) (by rw [hm, Bool.or_true])
  have hA : PlanAlike WP R.F := ProofFile.Honest.K14.planAlike_of_seat hS (LPFD.asks_written h4) hc h2
  obtain ⟨a, b, c', d, p0, p1, p2, hs, hB⟩ := atPure_book h
  obtain ⟨En, hEn⟩ := Johnson.AtFull.Sends.sendsWhole_all
  have t1 := VerifiableInference.Desc.LinkJoin.sends_tie O.pub hs
  have t2 := hEn _ (VerifiableInference.PlanWritten.Joined.made_in_scope hS O.pub hy)
  have hl := Except.ok.inj (t1.symm.trans t2)
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := hl
  obtain ⟨W, hW, hWa⟩ := bookWhole_returns_written_ahead
  have hC := bookWhole_carried_guess hA hW
  have hWR : W = R.B := Except.ok.inj (hC.symm.trans hB)
  exact ⟨by rw [← hWR]; exact hWa, (orderOf_alike hA.first hA.shared hA.second).symm⟩

/-- **THE DOOR AT A RETURN OF THE MAKER.** -/
theorem door_at_return (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R)
    (hO : okFast (firstPar qFull gpFull) (rideOf (firstFold qFull)) aheadBook (orderOf WP) oOpen = true)
    (hW : okFast (parW qFull gpFull 4 wMsgFull) (rideOf (wFold qFull.lin)) aheadBook (orderOf WP) oW =
      true)
    (hK : OwnersWritten) :
    ∀ e ∈ R.B.ahead, e.once = true → lotsMine R.Z R.G e.owner = true →
      lotsOkB R.Z R.G R.B (orderOf R.F) e.owner = true := by
  obtain ⟨hA, hOrd⟩ := ahead_at_ret hS hL h
  obtain ⟨Bs, base, c, A, B, O, hG⟩ := Johnson.M1.open_of_return h
  obtain ⟨h2, h4⟩ := plan_of_live hL O
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨hm, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  have hy := VerifiableInference.PlanWritten.pinnedAt_of_row (Z := R.Z) (by rw [hm, Bool.or_true])
  have hLZ := VerifiableInference.Desc.K13.Law.likeFull_in_scope hS O.pub hy
  have hg := VerifiableInference.Desc.K13.Law.gpOf_in_scope hS O.pub hy
  have hLG : VerifiableInference.Desc.K1.LikeFull Bs.G₀.first := by rw [O.first]; exact hLZ
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  have hv := Johnson.AtFull.Desc.K1Lot.view_in_scope hS hR O.pub O.blank
  rw [hOrd, ← hG]
  exact door_written hLG hLZ hg hv hO hW hK R.B hA

end AtFullSide.M1

#print axioms AtFullSide.M1.ahead_at_ret
#print axioms AtFullSide.M1.door_at_return
