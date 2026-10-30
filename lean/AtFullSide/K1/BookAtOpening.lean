-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/BookAtOpening.lean: the shared "sending" (the kind K1): THE BOOK's SIDE AT THE OPENING's
SENDER (the owner ⟨⟨1, some 0, 1, .K1⟩, 0⟩): in scope, where the gate accepts, at the book that the maker
onlineProverFromPublicFiles returns, at any filling, and at the returned description's own order of places, the wider
condition on the book BookClearAny (Johnson/SendSim/At/BookWide.lean) holds at that sender, at the
opening's own numbers and ride. Public data alone. No definition; seven theorems.

  lists_ok          ONE EVALUATION IN LEAN's KERNEL: the test listsOkB (Honest/K1/Sim/BookLists.lean)
                    accepts the 335 spending and the 209 carried entries (OpeningEntries.lean), at the
                    written numbers of the opening, its ride and the written order of places
  lists_early_no    the test can fail: the carrying of message 0 to the first closing, bent to a part
                    in front of the first spender
  lists_twice_no    the test can fail: one spending entry laid twice
  runs_not_rising   in the book's order the spending runs do not rise (so fastOkB rejects here), and no
                    two share a coin
  clear_written     BookClearAny at every book whose entries are rawAheadW, at the written letters
  order_at_head     under the library's head the description's order of places is the written one
  clear_at_opening  THE SAME AT THE MAKER's OWN BOOK, NUMBERS, RIDE AND ORDER

What lies there, in words: BY A PROGRAM OVER THE TWO LISTS, STATED BY NO THEOREM. The segment's mask row: 320 entries, coins 0 to 4058 of the
extension field, spent by 163 parts at the places 3 to 8 of the order; message 0, which holds that row,
its pads and tails, is carried first to the place 12. The table that rides: 17 coefficients from 8411,
spent by the first closing at the place 12; its message is carried from the place 16 on. The index-mask
message: 14 entries from 8647 to 8696, the last spent at the place 355; that message is carried to the
place 372 alone. No two spending runs share a coin.

Limits. All limits of BookLists.lean, OpeningEntries.lean and BookAtIdle.lean. The order is the
description's own: at another order nothing is said. The full size alone; the format's second hash function
alone. In the side library, because it imports files of it. No property of the protocol is claimed.
-/
import AtFullSide.K1.OpeningEntries
import AtFullSide.K1.BookAtIdle
import Johnson.Desc.ProofFile.Honest.K1.Sim.BookLists
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.HB.LLHARD.PlanInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.K1 (qFull)
open VerifiableInference.Desc.K13.Law (gpFull)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS F0T)
open ProofFile (Inst Pub Ground)
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K1.Sim ProofFile.Honest.K14
open AtFullSide.K14
open OnBytes.SendSim.At OnBytes.SendSim.Seat

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test accepts the two lists**, at the written letters. -/
theorem lists_ok :
    listsOkB (K1.firstPar qFull gpFull) (rideOf (firstFold qFull)) openS openC (orderOf WP) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail: a carrying of message 0's coins, at that message's true start and count, to a
part in front of the first spender: the sixth clause bites. -/
theorem lists_early_no :
    listsOkB (K1.firstPar qFull gpFull) (rideOf (firstFold qFull)) openS
      (⟨"x", opener, ⟨0, 0⟩, ⟨23214, 8411⟩, ⟨⟨1, some 0, 2, .K3⟩, 0⟩, false⟩ :: openC)
      (orderOf WP) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test can fail: the first spending entry laid twice. -/
theorem lists_twice_no :
    listsOkB (K1.firstPar qFull gpFull) (rideOf (firstFold qFull)) (openS.take 1 ++ openS) openC
      (orderOf WP) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Why fastOkB rejects at this owner though the book is clear**: in the book's order the spending runs
do not rise; yet no two share a coin. -/
theorem runs_not_rising :
    risingB (openS.map runE) = false ∧ apartAllB (openS.map runE) = true := by
  decide +kernel

/-- **BookClearAny at the opening's sender, at every book with the written entries**, at the written
letters. -/
theorem clear_written {B : ProverCoinCounts} (hB : B.ahead = rawAheadW) :
    BookClearAny (K1.firstPar qFull gpFull) (rideOf (firstFold qFull)) B (orderOf WP) opener :=
  clearAny_of_lists (by unfold spendsOf; rw [hB]; exact spends_open)
    (by unfold carriesOf; rw [hB]; exact carries_open) lists_ok

/-- Under the head the description's order of places is the written one. -/
theorem order_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : AtMgA o Z D r Zp Np cF x) :
    orderOf (F0T o Zp Np cF) = orderOf WP := by
  have pa := planAlike_at_head h
  unfold ProofFile.Honest.orderOf
  rw [alike₂_place _ _ pa.first, alike₂_place _ _ pa.shared, alike₂_place _ _ pa.second]

/-- **THE BOOK IS CLEAR AT THE OPENING's SENDER: AT THE MAKER's OWN BOOK, AT THE OPENING's OWN NUMBERS
AND RIDE, AT THE RETURNED DESCRIPTION's OWN ORDER.** -/
theorem clear_at_opening {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    BookClearAny (K1.firstPar A.G.first (K1.gpOf A.Z)) (rideOf (firstFold A.G.first)) A.B
      (orderOf A.F) ⟨⟨1, some 0, 1, .K1⟩, 0⟩ := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hS
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z hS hR hL (P5J.owed_of_live hL)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨m, -⟩ := K5.parts_of_atPure hA
  have eZ : A.Z = Zp := Except.ok.inj (m.pub.symm.trans O.pub)
  have eF : A.F = F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (m.desc.symm.trans h.laid.value)
  have eG : A.G = Bs.G₀ := by
    have g := m.ground
    rw [eZ] at g
    exact Option.some.inj (g.symm.trans O.blank)
  have hLZ := K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)
  have hg := K13.Law.gpOf_in_scope h.scope h.laid.pub (K1.pin1_atAll h)
  have hLG : K1.LikeFull A.G.first := by rw [eG, O.first]; exact hLZ
  have hfold : firstFold A.G.first = firstFold qFull := by
    unfold firstFold K1.frame₀
    rw [hLG.shape]
    rfl
  rw [K1.firstPar_full hLG, eZ, hg, hfold, eF, order_at_head h]
  exact clear_written (ahead_at_return hS hL hA)

end AtFullSide.K1

#print axioms AtFullSide.K1.lists_ok
#print axioms AtFullSide.K1.lists_early_no
#print axioms AtFullSide.K1.lists_twice_no
#print axioms AtFullSide.K1.runs_not_rising
#print axioms AtFullSide.K1.clear_written
#print axioms AtFullSide.K1.order_at_head
#print axioms AtFullSide.K1.clear_at_opening
