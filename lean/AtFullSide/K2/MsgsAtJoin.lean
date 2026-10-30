-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/MsgsAtJoin.lean: the kind "the code switch" (K2): THE FIELD msgs OF THE RECORD
`K2SeatedL` (Johnson/Desc/ProofFile/Honest/K2/SeatedL.lean), IN THE RECORD's OWN TERMS, AT THE
JOINED SCRIPT `joinQ`, AT EVERY MESSAGE OF EVERY SWITCH OF THE PLAN: THE KEPT COPIES TOO, BUT FOR
LINK 1's, WHICH STAY A PREMISE. Under the library's head, the opening and the book's return, at a
fit list that holds the kind's share. BY A WALK BACK ALONG THE LINKS: a message of which the switch
is the first sender: `msgs_first_at_join`; a kept copy: `ownMsgs_copy_at_head` from the tie at the
message that it copies, one link in front, which is a first sender's or again a kept copy. One
definition, a public number; four closed facts by evaluation in Lean's kernel; lemmas.

  `roundsCutW`, `roundsTo_at_head`   the rounds in front of a border, off the written cut
  `copyOrderW`      BY LEAN's KERNEL (no control): at each written pair the switch in front has no
                    more rounds in front of it than the one behind; and the numbers of the
                    challenges that the segments in front of it read lie below its own count
  `copyNumsW`       BY LEAN's KERNEL: a kept copy and the message that it copies have ONE NUMBER in
                    the witness; a control: against message 0 in front the test says no
  `pairsThereW`, `pair_of_place`   BY LEAN's KERNEL (no control): each written place from link 2 on
                    is the second of a written pair
  `keptLenW`        BY LEAN's KERNEL (no control): as many kept shapes as kept targets
  `h0_of_public`    where a switch's public test on the instance passes, the filling reads no
                    challenge at the switch's own messages
  `arr_seat`        the table's number at a message's seat is the plan's number of the message
  `msgs_at_join`    THE END

Limits. SIX PREMISES BESIDE THE HEAD, THE OPENING AND THE BOOK: F (the list is fit) · hin (it holds
the share) · hcl (each switch's closing passes its public test; a payer that is not called here:
`closing_at_head`, Johnson/Desc/ProofFile/Honest/K2/Law/ClosingAtHead.lean) · hpub (each switch's
public test on the instance passes at every input that is meant) · hD1 (how many challenges the
filling D reads at the addresses of the segments in front; at two switches one link apart alone) ·
hOne: THE TIE AT LINK 1's KEPT COPIES: these copy messages of the opening, which no switch sends:
NOTHING IS SHOWN OF THEM HERE. What `share_off_fit` says of the book, and what
`ownMsgs_copy_at_book` says of itself, hold here too. Whether a text answers is not said. The full
size and the format's second hash function alone. Nothing on any property.
-/
import AtFullSide.K2.CopyRunAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.TieAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.ReadyOfClosing
import Johnson.Desc.ProofFile.Honest.K5.Law.BaseAt
import Johnson.Desc.K2.Honest.Returns.UnderHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (keptNo)
open VerifiableInference.Desc.K2.Honest.Returns (tests_at_head)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.G (proofSendsFull)
open P5T (seatsAllFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread (TreeLot OwnMsgs Others joinQ JoinFit)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-! ## 1 At the written constants -/

/-- The rounds in front of border number b, off the written cut. -/
def roundsCutW (b : Nat) : Nat := ((cutFirstFull.take b).map (·.2.2.1)).sum

set_option maxRecDepth 1000000 in
/-- At each written pair: the order of the two counts; the challenges' numbers lie below. -/
theorem copyOrderW : (copyPairs.all fun x =>
    decide (roundsCutW (switchNo x.1) ≤ roundsCutW (switchNo x.2.1)) &&
      (segsW.take x.1.link).all fun Sg => Sg.gamma.all fun g =>
        decide (g < roundsCutW (switchNo x.1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A kept copy and the message that it copies have one number**; a control: against message 0 in
front the test says no at every copy. -/
theorem copyNumsW :
    (copyPairs.all fun x => (List.range x.2.1.sizes.kept.length).all fun i =>
      switchNumIn seatsAllFull x.2.1.link (1 + i) ==
        switchNumIn seatsAllFull x.1.link (keptNo (membersOfSeg x.2.2 true) i)) = true ∧
    (copyPairs.any fun x => (List.range x.2.1.sizes.kept.length).any fun i =>
      switchNumIn seatsAllFull x.2.1.link (1 + i) == switchNumIn seatsAllFull x.1.link 0) =
        false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each written place from link 2 on has a written place one link in front and a written segment
between. -/
theorem pairsThereW : (placesW.all fun p => decide (p.link < 2) ||
    ((placesW.find? fun a => a.link + 1 == p.link).isSome && (segsW[p.link - 1]?).isSome)) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- As many kept shapes as kept targets. -/
theorem keptLenW :
    (placesW.all fun p => p.sizes.kept.length == p.sizes.target.kept.size) = true := by
  decide +kernel

/-- Each written place from link 2 on is the second of a written pair. -/
theorem pair_of_place {p : SwitchPlace} (hp : p ∈ placesW) (h2 : 2 ≤ p.link) :
    ∃ p₀ S, (p₀, p, S) ∈ copyPairs := by
  have t := List.all_eq_true.1 pairsThereW p hp
  rw [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at t
  rcases t with t | ⟨t1, t2⟩
  · omega
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 t1
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 t2
    refine ⟨a, T, ?_⟩
    unfold copyPairs
    exact List.mem_filterMap.2 ⟨p, hp, by simp only [ha, hT]⟩

/-- **Where a switch's public test on the instance passes, the filling reads no challenge at the
switch's own messages.** -/
theorem h0_of_public {Xi : Type} {D : RowDataOf Xi} {lay : OnBytes.Params.ReqLayout}
    {p : SwitchPlace} {segs : List SegmentPub} {x : Xi} (h : publicOk D lay p segs x = true) :
    ∀ m, m < p.others.size - 1 → (D x).heardAt (p.ownAddr m) = 0 := by
  intro m hm
  have hl : ownLaid (D x) lay p segs = .ok () := by
    unfold publicOk at h
    cases e : ownLaid (D x) lay p segs with
    | ok u => rfl
    | error s =>
      rw [e] at h
      cases h
  have hlen : m < (p.others.toList.take (p.others.size - 1)).length := by
    rw [List.length_take, Array.length_toList]
    omega
  have hmem : ((p.others.toList.take (p.others.size - 1))[m], m) ∈
      (p.others.toList.take (p.others.size - 1)).zipIdx := by
    refine List.mem_of_getElem? (i := m) ?_
    rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hlen]
    simp
  exact heardAt_of_ready (ownLaid_ready hl _ hmem)

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- The rounds in front of a border are the written cut's. -/
theorem roundsTo_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) (b : Nat) : roundsTo cF.blocksInOrder b = roundsCutW b := by
  rw [K5.roundsTo_cut, (tests_at_head h.toAtMg O).2.1]
  rfl

/-- The table's number at a message's seat is the plan's number of the message. -/
theorem arr_seat (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    {n : Nat} (hn : n < (switchSent p.sizes p.others).size) :
    P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
        (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2 =
      switchNumIn seatsAllFull p.link n := by
  obtain ⟨q, hq, e1, -⟩ := share_seat h O hp hn
  rw [← e1, ← pseatsAll_at_head h.toAtMg]
  unfold switchNumIn
  rw [hq]
  rfl

variable {W₀ Rc Xi Tr Xj X Cells Tok : Type}
  {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {Oth : Others B (Local W₀ Rc Xi Tr)}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
  {rest : Nat → TreeLot B (Local W₀ Rc Xi Tr)}

/-- **THE FIELD msgs AT THE JOINED SCRIPT, AT EVERY MESSAGE OF EVERY SWITCH OF THE PLAN.** hOne: the
tie at link 1's kept copies: A PREMISE. -/
theorem msgs_at_join (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt B cF.blocksInOrder 0 Zp Bs.G₀ D readers rest) Oth)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop)
    (hcl : ∀ p ∈ switchPlaces Zp Bs.G₀,
      closingOk freshTable ((segmentsOf Zp Bs.G₀).take p.link) p = true)
    (hpub : ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ w, Vd w →
      publicOk D Bs.G₀.first.layout p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true)
    (hD1 : ∀ p₀ ∈ switchPlaces Zp Bs.G₀, ∀ p ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link →
      ∀ w, Vd w → ∀ s m a, s < p₀.link → p.addrs s m = some a →
        (D w.x).heardAt a ≤ 0 + roundsTo cF.blocksInOrder (switchNo p₀))
    (hOne : ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 → ∀ n, n < (switchPar p).sent.size →
      firstSender p n = false →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchPar p).sent.size →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) := by
  have eS := segments_at_head h.toAtMg O
  have eP := places_at_head h.toAtMg O
  have key : ∀ l, ∀ p ∈ switchPlaces Zp Bs.G₀, p.link = l → ∀ n, n < (switchPar p).sent.size →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro p hp hl n hn
      by_cases h1 : firstSender p n = true
      · exact msgs_first_at_join h O hp F hin cells tok Vd n hn h1
      · have h1' : firstSender p n = false := Bool.eq_false_iff.2 h1
        by_cases h2 : p.link < 2
        · exact hOne p hp h2 n hn h1'
        · have hpW : p ∈ placesW := by
            rw [← eP]
            exact hp
          obtain ⟨p₀, S, hx⟩ := pair_of_place hpW (by omega)
          obtain ⟨m₀, -, hlk, -⟩ := copyPair_mem hx
          have hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀ := by
            rw [eP]
            exact m₀
          unfold firstSender at h1'
          rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at h1'
          obtain ⟨i, rfl⟩ : ∃ i, n = 1 + i := ⟨n - 1, by omega⟩
          have hk : p.sizes.kept.length = p.sizes.target.kept.size :=
            beq_iff_eq.1 (List.all_eq_true.1 keptLenW p hpW)
          have hi : i < p.sizes.kept.length := by omega
          have hs₀ : (switchPar p₀).sent = switchSent p₀.sizes p₀.others := sendingPar_sent _ _
          have hs : (switchPar p).sent = switchSent p.sizes p.others := sendingPar_sent _ _
          have hn₀ : keptNo (membersOfSeg S true) i < (switchSent p₀.sizes p₀.others).size - 1 :=
            of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 copyNoW _ hx) i
              (List.mem_range.2 hi))
          have hm₀ := ih p₀.link (by omega) p₀ hp₀ rfl (keptNo (membersOfSeg S true) i)
            (by rw [hs₀]; omega)
          have tO := List.all_eq_true.1 copyOrderW _ hx
          rw [Bool.and_eq_true, decide_eq_true_eq] at tO
          have hf : 0 + roundsTo cF.blocksInOrder (switchNo p₀) ≤ 0 + roundsTo cF.blocksInOrder (switchNo p) := by
            rw [roundsTo_at_head h O, roundsTo_at_head h O]
            exact Nat.add_le_add_left tO.1 0
          have eN : P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) (1 + i)).1
              (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) (1 + i)).2 =
              P5J.At.arr Zp
                (seatAtMember cF.blocksInOrder (switchNo p₀) (switchPar p₀)
                  (keptNo (membersOfSeg S true) i)).1
                (seatAtMember cF.blocksInOrder (switchNo p₀) (switchPar p₀)
                  (keptNo (membersOfSeg S true) i)).2 := by
            rw [arr_seat h O hp (by rw [← hs]; exact hn), arr_seat h O hp₀ (by omega)]
            exact beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 copyNumsW.1 _ hx) i
              (List.mem_range.2 hi))
          rw [eN]
          rw [eS] at hm₀ ⊢
          exact ownMsgs_copy_at_head h O hB _ Vd _ _ _ _ _ D readers hx hi rfl hm₀ hf
            (by rw [← eS]; exact hcl p₀ hp₀)
            (fun w hw => by rw [← eS]; exact hpub p₀ hp₀ w hw)
            (fun w hw s m a hs' ha => hD1 p₀ hp₀ p hp hlk w hw s m a hs' ha)
            (fun w hw => h0_of_public (hpub p₀ hp₀ w hw))
            (fun Sg hSg g hg => by
              rw [roundsTo_at_head h O, Nat.zero_add]
              exact of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 tO.2 Sg hSg) g hg))
            hf hf
  exact fun p hp n hn => key p.link p hp rfl n hn

end AtFullSide.K2

#print axioms AtFullSide.K2.roundsCutW
#print axioms AtFullSide.K2.copyOrderW
#print axioms AtFullSide.K2.copyNumsW
#print axioms AtFullSide.K2.pairsThereW
#print axioms AtFullSide.K2.keptLenW
#print axioms AtFullSide.K2.pair_of_place
#print axioms AtFullSide.K2.h0_of_public
#print axioms AtFullSide.K2.roundsTo_at_head
#print axioms AtFullSide.K2.arr_seat
#print axioms AtFullSide.K2.msgs_at_join
