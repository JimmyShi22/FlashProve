-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TieAtJoin.lean: the kind "the code switch" (K2): THE TIE OF THE
RECORD `K2SeatedL` (Honest/K2/SeatedL.lean; its fields pads and msgs: premises on the script) AT THE
JOINED SCRIPT `joinQ` (Honest/Thread/Join.lean, of other authors), UNDER THE LIBRARY's HEAD AND THE
OPENING, AT EACH SWITCH OF THE PLAN, AT A FIT LIST THAT HOLDS THE KIND's SHARE: pads: AT EVERY
MESSAGE, in the record's own terms · msgs: AT THE MESSAGES OF WHICH THE SWITCH IS THE FIRST SENDER
ALONE. AT THE KEPT COPIES NOTHING IS SAID HERE. One definition, a public test; one closed fact by
evaluation in Lean's kernel, with a control; lemmas.

WHAT IS NEW. The ties themselves are `share_pads_fit` and `share_off_fit`
(Honest/K2/JoinShare.lean): they stand at the share's own letters: the tree and tenant that the
plan's list of seats gives, the number `switchNum`. The record asks at the seat `seatAtMember` and
at the table's number of that seat. HERE THE TWO ARE SHOWN TO BE ONE, PUBLICLY.

  `shareSeatOk`, `shareSeatsW`   A PUBLIC TEST: the plan's seat of the place's message n is the seat
                    that the verifier's book gives the sending's message n behind the written count
                    of trees, and it stands in the tree of message 0; BY LEAN's KERNEL at the
                    written lists; A CONTROL: one tree further it says no at each place
  `share_seat`      under the head: the seat, as an equation
  `pads_at_join`    THE FIELD pads
  `msgs_first_at_join`   THE FIELD msgs at a first sender

By: `share_pads_fit`, `share_off_fit`, `switchShareAt` (Honest/K2/JoinShare.lean) · `nums_switch`,
`countsAtSwitch` (Honest/K2/Law/SeatsAtSwitches.lean) · `pseatsAll_at_head`
(Honest/K2/Law/SwitchNumsAtHead.lean) · `borderNo_written` (Honest/K1/Law/MembersByBorder.lean, of
other authors) · `places_at_head` (Honest/K2/Law/PlacesWritten.lean) · `sendingPar_sent`
(Counts.lean).

Limits. F (the list is fit) AND hin (it holds the share) ARE PREMISES. WHAT `share_pads_fit` AND
`share_off_fit` SAY OF THE BOOK HOLDS HERE TOO: at a book whose count at the part's address does not
cover the part's due, or that does not lend it a stretch that it carries, these laws hold for
nothing: that the frame hands the part its coins is neither asked nor paid here: whoever quotes them
at a book names that at that book beside them. THE KEPT COPIES (messages 1 to the number of kept
targets): NOT SPOKEN OF. The front is 0, as the first thread's. The full size and the format's
second hash function alone. The head and the opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.SeatsAtSwitches
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (seatOfMsg)
open P5T (seatsAllFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread (TreeLot OwnMsgs OwnPads Others joinQ JoinFit)

/-! ## 1 At the written constants -/

/-- **A PUBLIC TEST** at a place, a count of trees and a message's number: the list's seat of the
place's message n is the seat that the book gives the sending's message n behind t trees, and it
stands in the tree of message 0. -/
def shareSeatOk (p : SwitchPlace) (t n : Nat) : Bool :=
  (switchSeatIn seatsAllFull p.link n).any fun q =>
    (q.j, q.t) == seatOfMsg (switchPar p) t n &&
      q.j == ((switchSeatIn seatsAllFull p.link 0).map (·.j)).getD 0

set_option maxRecDepth 1000000 in
/-- **At the written lists**; a control: one tree further the test says no at message 0 of each
place. -/
theorem shareSeatsW :
    (placesW.all fun p => (List.range (switchSent p.sizes p.others).size).all fun n =>
      shareSeatOk p (countsAtSwitch p).2 n) = true ∧
    (placesW.any fun p => shareSeatOk p ((countsAtSwitch p).2 + 1) 0) = false := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)} {p : SwitchPlace}

/-- **The seat, as an equation.** -/
theorem share_seat (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀)
    {n : Nat} (hn : n < (switchSent p.sizes p.others).size) :
    ∃ q, switchSeatIn (P5J.At.pseatsAll Zp) p.link n = some q ∧
      (q.j, q.t) = seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n ∧
      q.j = ((switchSeatIn (P5J.At.pseatsAll Zp) p.link 0).map (·.j)).getD 0 := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have t := List.all_eq_true.1 (List.all_eq_true.1 shareSeatsW.1 p hpW) n (List.mem_range.2 hn)
  unfold shareSeatOk at t
  rw [pseatsAll_at_head h.toAtMg]
  unfold seatAtMember
  rw [(nums_switch h O hp).2]
  cases e : switchSeatIn seatsAllFull p.link n with
  | none =>
    rw [e] at t
    cases t
  | some q =>
    rw [e] at t
    have t' : ((q.j, q.t) == seatOfMsg (switchPar p) (countsAtSwitch p).2 n &&
        q.j == ((switchSeatIn seatsAllFull p.link 0).map (·.j)).getD 0) = true := t
    rw [Bool.and_eq_true] at t'
    exact ⟨q, rfl, beq_iff_eq.1 t'.1, beq_iff_eq.1 t'.2⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xj X Cells Tok : Type}
  {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {Oth : Others Bk (Local W₀ Rc Xi Tr)}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
  {rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)}

/-- **THE FIELD pads AT THE JOINED SCRIPT**, in the record's own terms, at every message. -/
theorem pads_at_join (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) :
    ∀ n, n < (switchPar p).sent.size →
      OwnPads (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
        (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2
        (fun k _ => switchPadTxt 0 p n k) := by
  intro n hn
  have hn' : n < (switchSent p.sizes p.others).size := by
    rwa [show (switchPar p).sent = switchSent p.sizes p.others from sendingPar_sent _ _] at hn
  obtain ⟨q, hq, e1, e2⟩ := share_seat h O hp hn'
  unfold switchShareAt at hin
  have T := share_pads_fit (F := F) (hin := hin) (cells := cells) (tok := tok) (Vd := Vd)
    (hp := hp) (hn := hn')
  rw [← e1]
  have T' : OwnPads (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
      (((switchSeatIn (P5J.At.pseatsAll Zp) p.link 0).map (·.j)).getD 0)
      (((switchSeatIn (P5J.At.pseatsAll Zp) p.link n).map (·.t)).getD 0)
      (fun k _ => switchPadTxt 0 p n k) := T
  rw [← e2, hq] at T'
  exact T'

/-- **THE FIELD msgs AT THE JOINED SCRIPT**, in the record's own terms, AT A MESSAGE OF WHICH THE
SWITCH IS THE FIRST SENDER. -/
theorem msgs_first_at_join (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt Bk cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) :
    ∀ n, n < (switchPar p).sent.size → firstSender p n = true →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) := by
  intro n hn h1
  have hn' : n < (switchSent p.sizes p.others).size := by
    rwa [show (switchPar p).sent = switchSent p.sizes p.others from sendingPar_sent _ _] at hn
  obtain ⟨q, hq, e1, -⟩ := share_seat h O hp hn'
  unfold switchShareAt at hin
  have T := share_off_fit (F := F) (hin := hin) (cells := cells) (tok := tok) (Vd := Vd)
    (N := 0 + roundsTo cF.blocksInOrder (switchNo p)) (hp := hp) (hn := hn') (h1 := h1)
  have eN : switchNum Zp p n = P5J.At.arr Zp q.j q.t := by
    unfold switchNum switchNumIn
    rw [hq]
    rfl
  rw [← e1]
  have T' : OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
      (0 + roundsTo cF.blocksInOrder (switchNo p)) (switchNum Zp p n)
      (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
      (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) := T
  rw [eN, K1.borderNo_written h p.place] at T'
  exact T'

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.shareSeatOk
#print axioms ProofFile.Honest.K2.Law.shareSeatsW
#print axioms ProofFile.Honest.K2.Law.share_seat
#print axioms ProofFile.Honest.K2.Law.pads_at_join
#print axioms ProofFile.Honest.K2.Law.msgs_first_at_join
