-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ShrSeatsAt.lean: the closing of a segment (K10): under the head, at a state that the first chain's own sub-protocols reach in
front of a closing, without a mark of failure: the clauses on seats and shapes of the fields stand of `TieByShared` and `FreshByShared`
(Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieByShared.lean, XchFreshField.lean), at the plans of the shared sending (the kind K1), and the count
of the first segment's group that `threeLeft_at_first` (Pay/XchThreeLeft.lean) asks.

The sender's plans are taken at any first-chain parameters q with the written shape and codes (hs, hc), and any gp: as the laws on the book
take them (AtFullSide/K10/XchAtBookHead.lean).

  `shrPos_zero`, `shrPos_switch`   the place of the first later moment's message in the group's list: 3 at segment 0; at l ≥ 1 the number of the
                        code switch's messages less one
  **`shr_later_seats`**   each l < 25, both later moments (d): the group's member at that place has, in the state's book, the seat
                        `seatAtMember` of the sending's message 0, and that message's shape
  **`shr_open_seats`**    segment 0: the like for the opening's messages 0, 1, 2, at the places 0, 1, 2
  `shrMaskTest`, `shrMask_written`, `shrMask_bent`   a closed test, by Lean's kernel, with a control that fails: at the plan's number of segment 0's
                        fresh mask the written list of messages has the shape of the opening's message 3, and the written list of places
                        has its seat
  **`shr_mask_seat`**     segment 0: the fresh mask's message has the shape of the opening's message 3 and its seat
  **`shr_count_zero`**    segment 0: the group has at most 3 + 1 + 1 members

By: `member_at_closing`, `members_at_closing`, `seat_at_reach` (Pay/SeatsAtStand.lean); `mask_no_reached`, `mask_message` (Pay/FoldAt.lean);
`at_of_idx` (Pay/XchSeatsAt.lean); the closed tests of AtFullSide/K10/ShrSeats.lean; `treesTo_at_head` (Honest/K2/Law/PlacesWritten.lean);
`open_sent`, `later_sent` (AtFullSide/K10/XchAtBookShared.lean); `AtMg.seats_written` (Johnson/HB/LLHARD/MaskSeatWritten.lean).

Limits. The head is a premise; that the state is reached, has not failed and has the group is a premise. The full size and the older hash
alone. This file proves no property of a prover or a protocol.
-/
import AtFullSide.K10.ShrSeats
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSeatsAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.FoldAt
import Johnson.Desc.ProofFile.Honest.K1.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.First.Close (maskNo seatsPlanW)
open VerifiableInference.Desc.First.K2Hands (MList MW_eq)
open VerifiableInference.Desc.K12.Door (msgsOfChain msgShape_at)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.K1 (noL seatOfMsg firstPar parLater)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (seatBy noFirst)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (codesFull2)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.K2 (SwitchPlace switchSent)
open ProofFile.Honest.K2.Law (placesW treesTo_at_head)
open ProofFile.Honest.K10 (member_at_closing members_at_closing seat_at_reach at_of_idx mask_no_reached mask_message facts_reached)

theorem shrPos_zero : shrPosLater 0 = some 3 := rfl

theorem shrPos_switch {l : Nat} (h1 : 1 ≤ l) {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) :
    shrPosLater l = some ((switchSent p.sizes p.others).size - 1) := by
  unfold shrPosLater
  rw [if_neg (by omega), hp]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- One member, from its closed test. P: the sender's plan; sent: its messages, written. -/
theorem shr_member_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (hl : l < 25) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G)
    {P : VerifiableInference.Desc.K1.Par} {sent : Array OnBytes.OracleNotice} (hc : P.codes = codesFull2) (hs : P.sent = sent)
    {pos b n : Nat} (ht : shrMemberTest 0 l pos sent b n = true) {o : Nat} (ho : G.members.idxOf? o = some pos) :
    seatBy noFirst s.book o = some (seatAtMember cF.blocksInOrder b P n) ∧
      ∃ y, s.st.oracles[o]? = some y ∧ y.shape = shapeAt P n := by
  obtain ⟨i, hi, -, hseat, y, hy, hsh⟩ := member_at_closing h hl hr hf hG (at_of_idx ho)
  obtain ⟨i', hi', e1, e2⟩ := shrMember_says ht
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have w1 : P5J.At.pseats Zp = P5T.psFull := (P5J.AtMg.seats_written h.toAtMg).1
  refine ⟨?_, y, hy, ?_⟩
  · rw [hseat, w1, e1]
    show _ = some (seatOfMsg P (ProofFile.Honest.treesTo cF.blocksInOrder b) n)
    rw [seatOfMsg_is, treesTo_at_head h.toAtMg O b, hc, hs]
  · rw [hsh, e2]
    show _ = (P.sent.getD n default).shape
    rw [hs]

/-- **A later moment's message.** lo: its place in the group's list, in whatever spelling the caller has it. -/
theorem shr_later_seats (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (hl : l < 25)
    {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (gp : _root_.Desc.Plain.GPar)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) (d : Bool) {c lo : Nat}
    (hpos : shrPosLater l = some c) (hlo : lo = c + (if d then 1 else 0)) :
    ∀ n, n < 1 → ∀ o, G.members.idxOf? o = some (lo + n) →
      seatBy noFirst s.book o =
          some (seatAtMember cF.blocksInOrder (noL l d) (parLater q gp l (IM.k1Ix l d + 1) (if d then 2 else 1)) n) ∧
        ∃ y, s.st.oracles[o]? = some y ∧ y.shape = shapeAt (parLater q gp l (IM.k1Ix l d + 1) (if d then 2 else 1)) n := by
  intro n hn o ho
  obtain rfl : n = 0 := by omega
  rw [Nat.add_zero, hlo] at ho
  obtain ⟨c', hc', t1, t2⟩ := shrLater_says hl
  obtain rfl : c' = c := Option.some.inj (hc'.symm.trans hpos)
  cases d with
  | false => exact shr_member_at h hl hr hf hG hc (later_sent hs l _ 1) t1 ho
  | true => exact shr_member_at h hl hr hf hG hc (later_sent hs l _ 2) t2 ho

/-- **The opening's first three messages, at the first segment.** -/
theorem shr_open_seats (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (gp : _root_.Desc.Plain.GPar)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * 0 + IM.nAt 0 + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    ∀ n, n < 3 → ∀ o, G.members.idxOf? o = some (0 + n) →
      seatBy noFirst s.book o = some (seatAtMember cF.blocksInOrder 2 (firstPar q gp) n) ∧
        ∃ y, s.st.oracles[o]? = some y ∧ y.shape = shapeAt (firstPar q gp) n := by
  intro n hn o ho
  rw [Nat.zero_add] at ho
  exact shr_member_at h (by omega) hr hf hG hc (open_sent hs)
    (List.all_eq_true.1 shrOpen_written n (List.mem_range.2 hn)) ho

/-- The test on segment 0's fresh mask. e: a number added to the tenant that is asked for: 0 in the test. -/
def shrMaskTest (e : Nat) : Bool :=
  decide (MList[maskNo seatsPlanW P5T.psFull 0]? = some (sentOpen.getD 3 default).shape) &&
    decide (LFull.places[maskNo seatsPlanW P5T.psFull 0]? =
      some ((shrSeatS codesFull2 sentOpen (treesTold toldFull 2) 3).1,
        (shrSeatS codesFull2 sentOpen (treesTold toldFull 2) 3).2 + e))

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem shrMask_written : shrMaskTest 0 = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem shrMask_bent : shrMaskTest 1 = false := by decide +kernel

/-- **The first segment's fresh mask has the shape and the seat of the opening's message 3.** -/
theorem shr_mask_seat (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    {q : OnBytes.Params.First} (hs : q.shape = shapeFull) (hc : q.codes = codesFull2) (gp : _root_.Desc.Plain.GPar)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * 0 + IM.nAt 0 + 5) (z, s)) (hf : s.failed = none)
    {mk : Nat} (hm : (K9.recOf s).frame.mask = some mk) :
    (∀ y, s.st.oracles[mk]? = some y → y.shape = shapeAt (firstPar q gp) 3) ∧
      seatBy noFirst s.book mk = some (seatAtMember cF.blocksInOrder 2 (firstPar q gp) 3) := by
  obtain ⟨y₀, hy₀, -⟩ := mask_message h (by omega : 0 < 25) hr hf hm
  have hy₁ : s.st.oracles[mk]? = some y₀ := hy₀
  have hlt : mk < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hy₁).1
  obtain rfl : mk = maskNo seatsPlanW P5T.psFull 0 :=
    Option.some.inj (hm.symm.trans (mask_no_reached h.toAtMg (by omega : 0 < 25) hr))
  obtain ⟨a1, a2⟩ := Eq.mp (Bool.and_eq_true _ _) shrMask_written
  have a1' := of_decide_eq_true a1
  have a2' := of_decide_eq_true a2
  have hM := (facts_reached h hr hf).2.2.2.2
  have e3 : msgsOfChain Zp.made.proof.1 = MList := by
    rw [sends_in_scope h.toAtMg.scope h.toAtMg.laid.pub (P5J.pins_of_laid h.toAtMg.scope h.toAtMg.laid).1]
    exact MW_eq
  have hsx := msgShape_at (st := s.st) hM _ hlt
  rw [e3, a1'] at hsx
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨fun y hy => ?_, ?_⟩
  · rw [hy] at hsx
    show y.shape = ((firstPar q gp).sent.getD 3 default).shape
    rw [open_sent hs]
    exact Option.some.inj hsx
  · rw [seat_at_reach h (by decide) hr hf hlt a2']
    show _ = some (seatOfMsg (firstPar q gp) (ProofFile.Honest.treesTo cF.blocksInOrder 2) 3)
    rw [seatOfMsg_is, treesTo_at_head h.toAtMg O 2, open_sent hs]
    show _ = some (shrSeatS q.codes sentOpen (treesTold toldFull 2) 3)
    rw [hc]
    generalize shrSeatS codesFull2 sentOpen (treesTold toldFull 2) 3 = X
    rfl

/-- **The first segment's group has at most 3 + 1 + 1 members.** -/
theorem shr_count_zero (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * 0 + IM.nAt 0 + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    G.members.size ≤ 3 + 1 + 1 := by
  have hm := (members_at_closing h (by omega : 0 < 25) hr hf hG).1
  have e := congrArg List.length hm
  rw [Array.length_toList, List.length_map, shrCount_zero] at e
  exact Nat.le_of_eq e

end AtFullSide.K10

#print axioms AtFullSide.K10.shrPos_zero
#print axioms AtFullSide.K10.shrPos_switch
#print axioms AtFullSide.K10.shr_member_at
#print axioms AtFullSide.K10.shr_later_seats
#print axioms AtFullSide.K10.shr_open_seats
#print axioms AtFullSide.K10.shrMask_written
#print axioms AtFullSide.K10.shrMask_bent
#print axioms AtFullSide.K10.shr_mask_seat
#print axioms AtFullSide.K10.shr_count_zero
