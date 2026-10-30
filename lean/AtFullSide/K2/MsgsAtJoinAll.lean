-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/MsgsAtJoinAll.lean: the kind "the code switch" (K2): THE FIELD msgs OF THE RECORD
`K2SeatedL`, AT THE JOINED SCRIPT `joinQ`, AT EVERY MESSAGE OF EVERY SWITCH OF THE PLAN, LINK 1's
KEPT COPIES TOO: `msgs_at_join` (AtFullSide/K2/MsgsAtJoin.lean) WITH ITS PREMISE hOne GONE. In its
stead: hx: the opening's job stands with the number 2 in the list · hdat: on the two fillings. A
join. One definition, a public test; one closed fact by evaluation in Lean's kernel, with a control;
lemmas: calls.

  `firstNumsOk`, `firstNumsW`   A PUBLIC TEST at the written lists: at each written place below link
                    2: it stands at the number 2 or later in the written list of places; each of
                    its kept copies has, in the witness, the number of the opening's message that
                    it copies; BY LEAN's KERNEL; A CONTROL: against the opening's next message it
                    says no
  `firstNums_at`    what the test gives at a place of the plan below link 2
  `num_at_link_one`   hnum of `msgs_at_link_one`: one number at both seats
  `order_at_link_one`   hord: the opening has no more rounds in front of it than the switch
  `msgs_at_join_all`   THE END

By. Of this house: `msgs_at_join`, `arr_seat` (MsgsAtJoin.lean) · `msgs_at_link_one`, `firstCopiesW`
(MsgsAtLinkOne.lean) · `places_at_head` (Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean).
Of other authors, in the library: `seat_two_written`, `pseatsAll_written`
(Honest/K1/Law/K1NumAtHead.lean) · `roundsTo_mono` (Honest/Thread/ScriptFit.lean).

Limits. hdat IS A PREMISE, ON THE FILLINGS: at each input that is meant, at the opening's two
messages that link 1's kept copies copy, in range: the element over the base field that the sender's
filling DK lays, or 0, is the first coordinate of what the switch's filling D hands its closing
there: shown of no pair of fillings here. hx is a premise on the list. All other premises are
`msgs_at_join`'s, as they stand there: F · hin · hcl · hpub · hD1, beside the head, the opening and
the book. Whether a text answers is not said. A tie to a Script: what is WRITTEN where, at each
run's coins. The limits of the files called stand. NOT IN FRONT OF A LAW OVER COINS.
It speaks at the head's own size and hash: the full size, the format's second hash function. Nothing on any
property.
-/
import AtFullSide.K2.MsgsAtJoin
import AtFullSide.K2.MsgsAtLinkOne
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ScriptFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (firstPar gpOf parGF seatOfMsg)
open Johnson.G (proofSendsFull)
open P5T (seatsAllFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread (TreeLot OwnMsgs Others joinQ JoinFit)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- **A PUBLIC TEST** at the written lists. d: a bend for the control; 0 in earnest. -/
def firstNumsOk (d : Nat) : Bool :=
  (segsW[0]?).any fun Sg => (placesW.filter fun p => decide (p.link < 2)).all fun p =>
    decide (2 ≤ switchNo p) && (List.range p.sizes.target.kept.size).all fun i =>
      switchNumIn seatsAllFull p.link (1 + i) ==
        P5T.arrOf seatsAllFull
          (seatOfMsg parGF 0
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i + d)).1
          (seatOfMsg parGF 0
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i + d)).2

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test says yes**; a control: against the opening's next message it says no. -/
theorem firstNumsW : firstNumsOk 0 = true ∧ firstNumsOk 1 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- What the test gives at a place of the plan below link 2. -/
theorem firstNums_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀)
    (h2 : p.link < 2) {Sg : SegmentPub} (hSg : segsW[0]? = some Sg) :
    2 ≤ switchNo p ∧ ∀ i, i < p.sizes.target.kept.size →
      switchNumIn seatsAllFull p.link (1 + i) =
        P5T.arrOf seatsAllFull
          (seatOfMsg parGF 0
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)).1
          (seatOfMsg parGF 0
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)).2 := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hT := firstNumsW.1
  unfold firstNumsOk at hT
  rw [hSg] at hT
  have hT' := List.all_eq_true.1 (show ((placesW.filter fun p => decide (p.link < 2)).all _) = true
    from hT) p (List.mem_filter.2 ⟨hpW, decide_eq_true h2⟩)
  rw [Bool.and_eq_true] at hT'
  exact ⟨of_decide_eq_true hT'.1, fun i hi =>
    beq_iff_eq.1 (List.all_eq_true.1 hT'.2 i (List.mem_range.2 hi))⟩

/-- **One number at both seats**: hnum of `msgs_at_link_one`, in its own text. -/
theorem num_at_link_one (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 → ∀ Sg, segsW[0]? = some Sg →
      ∀ i, i < p.sizes.target.kept.size →
      P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) (1 + i)).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) (1 + i)).2 =
        P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)).1
          (seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)).2 := by
  intro p hp h2 Sg hSg i hi
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  -- the copy is a message of the sending: off the other closed test
  have hC := firstCopiesW.1
  unfold firstCopiesOk at hC
  rw [hSg] at hC
  have hC' := List.all_eq_true.1 (show ((placesW.filter fun p => decide (p.link < 2)).all _) = true
    from hC) p (List.mem_filter.2 ⟨hpW, decide_eq_true h2⟩)
  rw [Bool.and_eq_true] at hC'
  have hCi := List.all_eq_true.1 hC'.2 i (List.mem_range.2 hi)
  simp only [firstCopyOk, Bool.and_eq_true, decide_eq_true_eq] at hCi
  have hn : 1 + i < (switchSent p.sizes p.others).size := hCi.1.1.1.1.1.1.1.1.1.1.1.1.2
  rw [arr_seat h O hp hn, K1.seat_two_written h O, (firstNums_at h O hp h2 hSg).2 i hi]
  show _ = P5T.arrOf (P5J.At.pseatsAll Zp) _ _
  rw [K1.pseatsAll_written h]

/-- **The opening has no more rounds in front of it than the switch**: hord, in its own text. -/
theorem order_at_link_one (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 →
      roundsTo cF.blocksInOrder 2 ≤ roundsTo cF.blocksInOrder (switchNo p) := by
  intro p hp h2
  obtain ⟨Sg, hSg⟩ : ∃ Sg, segsW[0]? = some Sg := by
    have hT := firstNumsW.1
    unfold firstNumsOk at hT
    cases hq : segsW[0]? with
    | none =>
      rw [hq] at hT
      cases hT
    | some Sg => exact ⟨Sg, rfl⟩
  exact roundsTo_mono cF.blocksInOrder 2 (switchNo p) (firstNums_at h O hp h2 hSg).1

variable {W₀ Rc Xi Tr Xj X Cells Tok : Type}
  {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {Oth : Others B (Local W₀ Rc Xi Tr)}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}
  {rest : Nat → TreeLot B (Local W₀ Rc Xi Tr)}

/-- hdat IS A PREMISE. **THE FIELD msgs AT THE JOINED SCRIPT, AT EVERY MESSAGE OF EVERY SWITCH OF
THE PLAN, LINK 1's KEPT COPIES TOO.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem msgs_at_join_all (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
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
    {f₀ : Nat} {DK : RowDataOf Xj}
    (hx : (2, K1.placeJob (X := X) (firstPar Bs.G₀.first (gpOf Zp)) f₀ (K1.firstFold Bs.G₀.first)
      DK) ∈ jobs)
    (hdat : ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 → ∀ Sg, segsW[0]? = some Sg →
      ∀ i, i < p.sizes.target.kept.size → ∀ w, Vd w →
      ∀ (hd : List Fmt.Drawn) (fr : Front X), fr.heard = hd.take (0 + roundsTo cF.blocksInOrder 2) →
      ∀ a b, a < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows →
      b < (p.sizes.codes.base.getD
        ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell →
      (match (K1.placeJob (X := X) (firstPar Bs.G₀.first (gpOf Zp)) f₀
          (K1.firstFold Bs.G₀.first) DK).data (wit w) fr
          (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) a b with
        | some (.inl x) => x | _ => (0 : Cb.Gl.F)) =
      (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w)
        ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).take
          ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).length - 0)) (0 + 0)
        (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) a b).c0) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchPar p).sent.size →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) :=
  msgs_at_join h O hB F hin cells tok Vd hcl hpub hD1
    (msgs_at_link_one h O hB F cells tok Vd hx (num_at_link_one h O) (order_at_link_one h O) hdat)

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.firstNumsOk
#print axioms AtFullSide.K2.firstNumsW
#print axioms AtFullSide.K2.firstNums_at
#print axioms AtFullSide.K2.num_at_link_one
#print axioms AtFullSide.K2.order_at_link_one
#print axioms AtFullSide.K2.msgs_at_join_all
