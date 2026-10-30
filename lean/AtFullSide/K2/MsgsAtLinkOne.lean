-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/MsgsAtLinkOne.lean: the kind "the code switch" (K2): THE TIE ON THE SCRIPT's MESSAGES
AT LINK 1's KEPT COPIES, AT THE JOINED SCRIPT `joinQ`: the premise hOne of `msgs_at_join`
(AtFullSide/K2/MsgsAtJoin.lean), in its own text. These copies copy messages of the opening, which
no switch sends: their sender is the first job of the kind K1. Under the library's head, the opening
and the book's return, at a fit list in which that job stands with the number 2. It lies in the side
library because it imports files of it. Two definitions, public tests; one closed fact by evaluation
in Lean's kernel, with a control and a count; lemmas.

  `rowsR_mainF_data`   a main entry over the base field of the shared sending's rows reads of the
                    data the one element there, and 0 where none over the base field is laid
  `firstCopyOk`, `firstCopiesOk`, `firstCopiesW`   A PUBLIC TEST at a written place, a written
                    segment and a kept copy: the sizes, shapes and numbers that the law at one run
                    asks; BY LEAN's KERNEL at the one written place below link 2, against the first
                    written segment; A CONTROL: against the second it says no; A COUNT: that place
                    keeps two
  `msgs_at_link_one`   THE END

How. Where the copy's text answers, the switch was handed its stretches and laid its rows
(`msgTxt_inv`). The sender's own coins are there: the book covers them (`opening_covers_at_book`).
The rows that the closing lays anew of the first segment are the sender's rows at the switch's
reading of the data (`opening_rows_at_25`); their main entries are those at the sender's own
reading: hdat, A PREMISE. So the sender's text answers the same (`msgOff_copy_is_firsts`), and the
sender's tie (`join_tie_k1_fit`) gives the end, at one number in the witness: hnum, A PREMISE.

By. Of this house: `msgOff_copy_is_firsts`
(Johnson/Desc/ProofFile/Honest/K2/Law/MsgOffCopyFirst.lean) · `opening_rows_at_25`
(AtFullSide/K2/OpeningRowsAtTheBook.lean) · `opening_covers_at_book`
(AtFullSide/K11/OpeningCoversAtTheBook.lean) · `first_ties_at_head`
(Honest/K2/Law/K1SendersTies.lean) · `segmentRows_members` (GroupMembers.lean) · `msgTxt_inv`
(MainTxt.lean) · `noWord_yes` (Counts.lean) · `places_at_head`, `segments_at_head`
(PlacesWritten.lean). Of other authors: `join_tie_k1_fit` (Honest/Thread/JoinFit.lean) ·
`K1.lentCut_isSome` (Honest/K1/ScriptAtLaw.lean). Kin of `rowsR_mainF_data`, no twin: `rowsR_congr`
(Honest/K12/RowsCongr.lean): whole rows, from coins alike.

Limits. THREE PREMISES BESIDE THE HEAD, THE OPENING, THE BOOK, F AND hx: hnum: the table arr gives
one number at the copy's seat and at the seat of the opening's message: public; not paid here ·
hord: the opening has no more rounds in front of it than the switch: public; not paid here · hdat:
ON THE FILLINGS: at each input that is meant, at the opening's message that a kept copy copies and
no other, inside that message's rows and the code's length: the element over the base field that the
sender's filling DK lays, or 0 where it lays none, is the first coordinate of what the switch's
filling D hands its closing there: shown of no pair of fillings here. Whether a text answers is not
said. A tie to a Script: what is WRITTEN where, at each run's coins: no sentence on what an element
is for. The limits of the files called stand. NOT IN FRONT OF A LAW OVER COINS. It
speaks at the head's own size and hash: the full size, the format's second hash function. Nothing on any
property.
-/
import AtFullSide.K2.OpeningRowsAtTheBook
import AtFullSide.K11.OpeningCoversAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.MsgOffCopyFirst
import Johnson.Desc.ProofFile.Honest.K2.Law.K1SendersTies
import Johnson.Desc.ProofFile.Honest.K2.Law.GroupMembers
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain padB)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (proofSendsFull)
open OnBytes.Maker (WholeD)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (Others joinQ JoinFit join_tie_k1_fit OwnMsgs)
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 General -/

/-- A main entry over the base field reads of the data the one element there. -/
theorem rowsR_mainF_data (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data data' : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (c : Cs (K1.dueR P ride))
    (n r j : Nat)
    (hv : (match data n r j with | some (.inl x) => x | _ => (0 : Cb.Gl.F)) =
      (match data' n r j with | some (.inl x) => x | _ => (0 : Cb.Gl.F))) :
    (K1.rowsR P ride data c n).mainF r j = (K1.rowsR P ride data' c n).mainF r j := by
  simp only [K1.rowsR]
  split
  · rfl
  · split
    · rfl
    · exact hv

/-! ## 2 At the written constants -/

/-- **A PUBLIC TEST** at a place, a segment and a kept copy's number. -/
def firstCopyOk (p : SwitchPlace) (Sg : SegmentPub) (i : Nat) : Bool :=
  let s := ((switchSent p.sizes p.others).getD (1 + i) default).shape
  let ms := membersOfSeg Sg false
  let n := VerifiableInference.Desc.K2.Honest.keptNo ms i
  decide (i < p.sizes.kept.length) && decide (1 + i < (switchSent p.sizes p.others).size) &&
    !(s.mainDeg == 3) && s.maskRows == 0 && s.answers == 1 && decide (0 < s.mainRows) &&
    decide ((K1.stepsOf p.sizes.codes s none).pad ≤ (p.sizes.codes.base.getD s.code default).ell) &&
    decide ((Sg.sizes.codes.base.getD Sg.sizes.code default).ell =
      (p.sizes.codes.base.getD s.code default).ell) &&
    decide (i < ((ms.filter (·.kept)).map (·.shape)).length) &&
    ((ms.filter (·.kept)).map (·.shape)).getD i {} == s &&
    VerifiableInference.Desc.K2.Honest.shapeOf ms n == ((Sg.sent.headD #[]).getD n default).shape &&
    ((Sg.sent.headD #[]).getD n default).shape == s &&
    decide (n < (Sg.sent.headD #[]).size - 1) && Sg.sizes.codes == p.sizes.codes

/-- The same at each written place below link 2 and each of its kept copies, against the written
segment number d. -/
def firstCopiesOk (d : Nat) : Bool :=
  (segsW[d]?).any fun Sg => (placesW.filter fun p => decide (p.link < 2)).all fun p =>
    p.link == 1 && noWord (switchSent p.sizes p.others) &&
      (List.range p.sizes.target.kept.size).all fun i => firstCopyOk p Sg i

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Against the first written segment the test says yes**; a control: against the second it says
no; a count: one written place lies below link 2, and it keeps two. -/
theorem firstCopiesW : firstCopiesOk 0 = true ∧ firstCopiesOk 1 = false ∧
    ((placesW.filter fun p => decide (p.link < 2)).map fun p => p.sizes.target.kept.size) =
      [2] := by
  decide +kernel

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {B : ProverCoinCounts}
  {W₀ Rc Xi Tr Xj X Cells Tok : Type}
  {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xj} {own₀ : X}
  {jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) X)} {Oth : Others B (Local W₀ Rc Xi Tr)}
  {D : RowDataOf Xi} {readers : Local W₀ Rc Xi Tr → Readers}

set_option maxHeartbeats 1000000 in
/-- hnum, hord AND hdat ARE PREMISES. **THE TIE AT LINK 1's KEPT COPIES, AT THE JOINED SCRIPT**: the
premise hOne of `msgs_at_join`, in its own text.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem msgs_at_link_one (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀ jobs Oth)
    (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (Vd : Local W₀ Rc Xi Tr → Prop) {f₀ : Nat} {DK : RowDataOf Xj}
    (hx : (2, K1.placeJob (X := X) (firstPar Bs.G₀.first (gpOf Zp)) f₀ (K1.firstFold Bs.G₀.first)
      DK) ∈ jobs)
    (hnum : ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 → ∀ Sg, segsW[0]? = some Sg →
      ∀ i, i < p.sizes.target.kept.size →
      P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) (1 + i)).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) (1 + i)).2 =
        P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)).1
          (seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
            (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)).2)
    (hord : ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 →
      roundsTo cF.blocksInOrder 2 ≤ roundsTo cF.blocksInOrder (switchNo p))
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
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 → ∀ n, n < (switchPar p).sent.size →
      firstSender p n = false →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀ jobs Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 D readers (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) := by
  intro p hp h2 n' _ hfs
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  -- the copy's number
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < p.sizes.target.kept.size ∧ n' = 1 + i := by
    unfold firstSender at hfs
    rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not] at hfs
    exact ⟨n' - 1, by omega, by omega⟩
  -- the closed test
  have hT := firstCopiesW.1
  unfold firstCopiesOk at hT
  obtain ⟨Sg, hSg⟩ : ∃ Sg, segsW[0]? = some Sg := by
    cases hq : segsW[0]? with
    | none =>
      rw [hq] at hT
      cases hT
    | some Sg => exact ⟨Sg, rfl⟩
  rw [hSg] at hT
  have hT : ((placesW.filter fun p => decide (p.link < 2)).all fun p =>
      p.link == 1 && noWord (switchSent p.sizes p.others) &&
        (List.range p.sizes.target.kept.size).all fun i => firstCopyOk p Sg i) = true := hT
  have hTp := List.all_eq_true.1 hT p (List.mem_filter.2 ⟨hpW, decide_eq_true h2⟩)
  rw [Bool.and_eq_true, Bool.and_eq_true] at hTp
  obtain ⟨⟨hl1, hnw⟩, hall⟩ := hTp
  have hl : p.link = 1 := beq_iff_eq.1 hl1
  have hTi := List.all_eq_true.1 hall i (List.mem_range.2 hi)
  simp only [firstCopyOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_true'] at hTi
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩, t12⟩, t13⟩, t14⟩ :=
    hTi
  have hsegs := segments_at_head h.toAtMg O
  have hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg := by rw [hsegs]; exact hSg
  have hA : (segmentsOf Zp Bs.G₀).take p.link = [Sg] := by
    rw [hl]
    cases hq : segmentsOf Zp Bs.G₀ with
    | nil => rw [hq] at hS; cases hS
    | cons a l =>
      rw [hq] at hS
      obtain rfl : a = Sg := Option.some.inj hS
      rfl
  have KT := first_ties_at_head h O hS t13
  rw [hnum p hp h2 Sg hSg i hi]
  have T1 := (join_tie_k1_fit F cells tok Vd hx).1
    (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) KT.hq
  intro k w hd hv hN mask a b y hy
  refine T1 k w hd hv (Nat.le_trans (Nat.add_le_add_left (hord p hp h2) 0) hN) mask a b y ?_
  -- the run
  have hy' := hy
  unfold switchMsgOff at hy'
  by_cases hpb : padB p.sizes.codes ((switchSent p.sizes p.others).getD (1 + i) default).shape mask
      a b = true
  · rw [if_pos hpb] at hy'
    cases hy'
  rw [if_neg hpb] at hy'
  obtain ⟨c, V, hH, hV⟩ := msgTxt_inv hy'
  obtain ⟨cs, hcut⟩ := Option.isSome_iff_exists.1
    ((K1.lentCut_isSome k 0 (by omega) ⟨(firstPar Bs.G₀.first (gpOf Zp)).place, 0⟩
      (K1.dueR (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first)))).trans
      (AtFullSide.K11.opening_covers_at_book h O hB))
  refine msgOff_copy_is_firsts 0 D readers p k w _ _ hH hV hA (noWord_yes hnw) t1 t2 t3 t4 t5 t6 t7
    wit (K1.placeJob (X := X) (firstPar Bs.G₀.first (gpOf Zp)) f₀ (K1.firstFold Bs.G₀.first) DK)
    own₀ hcut (KT.hs.trans t12) (KT.hc.trans t14) KT.hride t8 ?_ mask a b y hy
  intro R hR
  have hM : R.members = membersOfSeg Sg false := segmentRows_members hR
  rw [hM]
  refine ⟨t9, t10, rfl, t11.trans KT.hs.symm, _,
    ((opening_rows_at_25 h O hB hS).2.2.2 p hp 0 k c hH none [] _ R hR cs hcut
      (fun m => asShared (shapeAt (firstPar Bs.G₀.first (gpOf Zp)) m)
        (dataAtOf Sg none _ m))).1 _ t13 rfl, ?_⟩
  intro a' b' ha' hb'
  refine rowsR_mainF_data _ _ _ _ cs _ a' b' ?_
  refine Eq.trans ?_ (hdat p hp h2 Sg hSg i hi w hv hd _ rfl a' b' ha' hb').symm
  unfold asShared
  rw [KT.hs, t12, t3]
  rfl

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.rowsR_mainF_data
#print axioms AtFullSide.K2.firstCopyOk
#print axioms AtFullSide.K2.firstCopiesOk
#print axioms AtFullSide.K2.firstCopiesW
#print axioms AtFullSide.K2.msgs_at_link_one
