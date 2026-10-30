-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchGHead.lean: the closing of a segment (K10): the clause on data in the field stand of `TieByShared` (Pay/XchTieByShared.lean) under
the library's head and the opening, at the filling `widerRows`: the public facts of `data_later` and `data_first` (Pay/XchGData.lean)
are paid: by closed tests on the written segments, addresses, plans and seats, and by the laws on the filling.

  `adL`, `tOf`, `laterPos`   the address of the one message of segment l's moment 1 (d = false) or 2 (d = true); 0 or 1; the place of
                     moment 1's message in the group's list
  `dataLaterB`, `dataLater_written`, `dataLater_bent`   at each written segment: two later sendings of one message each; each message's shape is
                     the written plan's; its address and its shape among the segment's own messages. By Lean's kernel; a control
  `dataHeardB`, `dataHeard_written`, `dataHeard_bent`   which filling answers at the two addresses, and that the seat's count of challenges is at
                     most the written count of rounds in front of the sending
  `dataFirstB`, `dataFirst_written`, `dataFirst_bent`   the like at the first segment's first three messages
  `lotData_heardAt`   which count the shared kind's filling states, by the address
  `heardAt_later`, `heardAt_first`   that count at our addresses
  **`data_later_head`**, **`data_first_head`**   the clause

Limits. The head and the opening are hypotheses. The full size and the older hash alone. Shapes, addresses and counts alone: nothing
on what the data hold.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchGData
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchPublic
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnStand
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeDigitsAt
import Johnson.Desc.ProofFile.Honest.AtPureWider
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnDataApart
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.HonestTrace.U3Fit.Slice

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K1 (noL placeL parGF)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz seatsOf mineOf heardOf bzRows)
open OnBytes.HonestTrace.U3 (u3RowsOf u3Seats)
open OnBytes.HonestTrace.U3.Fit (seatsW seats_at_head rowsBeforeW roundsTo_at_head)
open ProofFile.Honest.K2 (SegmentPub segmentsOf asRow mineDigits)
open ProofFile.Honest.K2.Law (Laid segsW addrsW seatsBZW mineDigitsW mineDigits_at_head seatsBZ_at_head
  segments_at_head with_other_kind)
open ProofFile.Honest.K8 (zzDataAt)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 At written values -/

/-- The address of the one message of segment l's moment 1 (d = false) or 2 (d = true). -/
def adL (l : Nat) (d : Bool) : MsgAddr := ⟨⟨⟨1, some l, IM.k1Ix l d + 1, .K1⟩, 0⟩, 0⟩

def tOf (d : Bool) : Nat := if d then 1 else 0

/-- The place of moment 1's message in the list of segment l's group. -/
def laterPos (l : Nat) : Nat := ((segsW[l]?).map fun S => (S.sent.headD #[]).size - 1).getD 0

/-- The first message of a segment's sending number i. -/
def msgOf (S : SegmentPub) (i : Nat) : OnBytes.OracleNotice := (S.sent.getD i #[]).getD 0 default

/-- The test at segment l. e: a shift of the number among the own messages, for the control. -/
def dataLaterB (e l : Nat) : Bool :=
  (segsW[l]?).any fun S =>
    decide (S.sent.drop 1 = [#[msgOf S 1], #[msgOf S 2]]) &&
      [false, true].all fun d =>
        decide (([msgOf S 1, msgOf S 2].getD (tOf d) default).shape = shapeAt (placeL l d) 0) &&
          decide (addrsW l (ownBase S (decide (0 < l)) + tOf d + e) = some (adL l d)) &&
          decide ((S.ownShapes (l == 0)).getD (ownBase S (decide (0 < l)) + tOf d) {} =
            shapeAt (placeL l d) 0)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem dataLater_written : ((List.range 25).all (dataLaterB 0)) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: one own message further on the test says no at every segment. -/
theorem dataLater_bent : ((List.range 25).any (dataLaterB 1)) = false := by decide +kernel

/-- Which filling answers at the two addresses, and the seats' counts. c: a shift of the border, for the
control. -/
def dataHeardB (c l : Nat) : Bool :=
  !((adL l false).sender == K1.firstAddr) && !mineOf seatsBZW (adL l false) &&
    decide (heardOf (seatsW "U3") (adL l false) + c ≤ rowsBeforeW (noL l false)) &&
    !((adL l true).sender == K1.firstAddr) && mineDigitsW (adL l true) &&
    decide (heardOf seatsBZW (adL l true) + c ≤ rowsBeforeW (noL l true))

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem dataHeard_written : ((List.range 25).all (dataHeardB 0)) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: the counts are the borders' own: one more and the test says no at every segment. -/
theorem dataHeard_bent : ((List.range 25).any (dataHeardB 1)) = false := by decide +kernel

/-- The test at the first segment's first three messages. e: a shift of the number among the own messages, for
the control. -/
def dataFirstB (e : Nat) : Bool :=
  (segsW[0]?).any fun S =>
    decide ((S.sent.headD #[]).size - 1 = 3) &&
      (List.range 3).all fun n =>
        decide (((S.sent.headD #[])[n]?).map (·.shape) = some (shapeAt parGF n)) &&
          decide (addrsW 0 (n + e) = some ⟨K1.firstAddr, n⟩) &&
          decide ((S.ownShapes true).getD n {} = shapeAt parGF n)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem dataFirst_written : dataFirstB 0 = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: one own message further on the test says no. -/
theorem dataFirst_bent : dataFirstB 1 = false := by decide +kernel

/-! ## 2 The filling's count of challenges -/

/-- Which count the shared kind's filling states, by the address. -/
theorem lotData_heardAt (S : Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst) (a : MsgAddr) :
    (K1.lotData S Z G x).heardAt a =
      if a.sender == K1.firstAddr then (K1.firstFill S G.first).heardAt a
      else if mineOf (seatsOf Z G "BZ") a then (K1.digitsFill Z G (K3.matsOwn G.W)).heardAt a
      else (u3RowsOf Z G x).heardAt a := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

theorem heardAt_first (S : Sz) (Z : Pub) (G : Ground) (ξ : ProofFile.Inst) (n : Nat) :
    (K1.lotData S Z G ξ).heardAt ⟨K1.firstAddr, n⟩ = 0 := by
  rw [lotData_heardAt, if_pos (beq_self_eq_true K1.firstAddr)]
  rfl

/-- **The data of a later moment's message read no challenge behind its sending's border.** -/
theorem heardAt_later (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (hl : l < 25) (d : Bool) (S : Sz) (ξ : ProofFile.Inst) :
    (K1.lotData S Zp Bs.G₀ ξ).heardAt (adL l d) ≤ roundsTo cF.blocksInOrder (noL l d) := by
  have t := List.all_eq_true.1 dataHeard_written l (List.mem_range.2 hl)
  unfold dataHeardB at t
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Nat.add_zero] at t
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := t
  rw [lotData_heardAt, roundsTo_at_head h]
  cases d with
  | false =>
    rw [if_neg (by rw [c1]; exact Bool.false_ne_true), seatsBZ_at_head h O,
      if_neg (by rw [c2]; exact Bool.false_ne_true)]
    show heardOf (u3Seats Zp Bs.G₀) (adL l false) ≤ _
    unfold u3Seats
    rw [seats_at_head h O.blank "U3"]
    exact c3
  | true =>
    have hm : mineDigits Zp Bs.G₀ (adL l true) = true := by
      rw [mineDigits_at_head h O]
      exact c5
    have hmine : mineOf (seatsOf Zp Bs.G₀ "BZ") (adL l true) = true := by
      unfold mineDigits at hm
      exact (Eq.mp (Bool.and_eq_true _ _) hm).2
    rw [if_neg (by rw [c4]; exact Bool.false_ne_true), if_pos hmine]
    obtain ⟨s, b, tl, dd, hs, -, -, -, -, hr1, -, -, -, -, hrng, -, -⟩ := digitsFit_at_head h O hm
    have e1 := bz_heardAt (mats := K3.matsOwn Bs.G₀.W) hs
    have eH : heardOf seatsBZW (adL l true) = s.heard := by
      rw [← seatsBZ_at_head h O]
      unfold heardOf
      rw [hs]
      rfl
    rw [eH] at c6
    show max ((bzRows Zp Bs.G₀ (K3.matsOwn Bs.G₀.W)).heardAt (adL l true))
      ((zzDataAt Bs.G₀ Zp.D.1 (OnBytes.HonestTrace.pairOf (seatsOf Zp Bs.G₀ "BZ"))
        (K3.matsOwn Bs.G₀.W)).heardAt (adL l true)) ≤ _
    rw [e1]
    rcases zz_heardAt (mats := K3.matsOwn Bs.G₀.W) hs hrng with ⟨e2, -⟩ | ⟨e2, -⟩
    · rw [e2, hr1, Nat.max_self]
      exact c6
    · rw [e2, Nat.max_eq_left (Nat.zero_le _)]
      exact c6

/-! ## 3 The clause -/

variable {W₀ Rc Tr : Type}

/-- What is public of the job's segments at closing l. -/
theorem lot_shape (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (hl : l < 25) {Qc : Par} (hQ : Qc.link = l) :
    (lotSegs Zp Bs.G₀ Qc).getLast? = segsW[l]? ∧ (lotSegs Zp Bs.G₀ Qc).length - 1 = l ∧
      (lotSegs Zp Bs.G₀ Qc)[l]? = segsW[l]? ∧
      (!(lotSegs Zp Bs.G₀ Qc).dropLast.isEmpty) = decide (0 < l) := by
  have hS := segments_at_head h.toAtMg O
  have eS : lotSegs Zp Bs.G₀ Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Bs.G₀).take (Qc.link + 1) = _
    rw [hS, hQ]
  have hlen : (segsW.take (l + 1)).length = l + 1 := by
    rw [List.length_take, segs_count]
    omega
  refine ⟨lot_last hS hQ hl, by rw [eS, hlen]; rfl, by
    rw [eS, List.getElem?_take_of_lt (Nat.lt_succ_self l)], ?_⟩
  rw [lot_front hS hQ hl]
  have hl2 : (segsW.take l).length = l := by
    rw [List.length_take, segs_count]
    omega
  cases hX : segsW.take l with
  | nil =>
    rw [hX] at hl2
    have : l = 0 := hl2.symm
    subst this
    rfl
  | cons y ys =>
    rw [hX] at hl2
    have : 0 < l := by
      rw [← hl2]
      exact Nat.succ_pos _
    rw [decide_eq_true this]
    rfl

/-- **THE CLAUSE ON DATA AT A LATER MOMENT's MESSAGE.** fr: any count of challenges from the sending's border on that
has been heard. -/
theorem data_later_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (hl : l < 25) (d : Bool) {Qc : Par}
    (hQ : Qc.link = l) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (S : Sz)
    {w : Local W₀ Rc ProofFile.Inst Tr} {heard : List Fmt.Drawn}
    {ca : CsAll (closeCarries ⟨Qc, borneAt Zp Qc⟩)} {a : Laid} {nn fr : Nat}
    (hle : roundsTo cF.blocksInOrder (noL l d) ≤ fr) (hfr : fr ≤ heard.length)
    (hL : LotMember readers (widerRows S Zp Bs.G₀) Zp Bs.G₀ Qc w heard ca (laterPos l + tOf d) a nn) :
    a.1 = shapeAt (placeL l d) 0 ∧
      a.2 = fun r j => asRow ((shapeAt (placeL l d) 0).mainDeg == 3)
        ((K1.lotData S Zp Bs.G₀ w.x).at_ (readers w) (heard.take fr) (adL l d) r j) := by
  obtain ⟨g1, g2, g3, g4⟩ := lot_shape h O hl hQ
  have t := List.all_eq_true.1 dataLater_written l (List.mem_range.2 hl)
  unfold dataLaterB at t
  obtain ⟨Sg, hSg⟩ : ∃ Sg, segsW[l]? = some Sg := by
    cases e : segsW[l]? with
    | none =>
      rw [e] at t
      cases t
    | some Sg => exact ⟨Sg, rfl⟩
  rw [hSg, Option.any_some, Bool.and_eq_true] at t
  obtain ⟨t1, t2⟩ := t
  have t3 := List.all_eq_true.1 t2 d (by cases d <;> simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero] at t3
  obtain ⟨⟨u1, u2⟩, u3⟩ := t3
  have hpos : laterPos l = (Sg.sent.headD #[]).size - 1 := by
    unfold laterPos
    rw [hSg]
    rfl
  rw [hpos] at hL
  refine data_later (D' := K1.lotData S Zp Bs.G₀ w.x) (g1.trans hSg) (of_decide_eq_true t1)
    (by cases d <;> decide) hL u1 ?_ ?_ ?_ (Nat.le_trans (heardAt_later h O hl d S w.x) hle) hfr
  · rw [g2, g4, addrs_at_head h O]
    exact u2
  · rw [g2, g3, g4, hSg]
    exact u3
  · intro hd r j
    exact (with_other_kind S (K1.lotData S) Zp Bs.G₀ w.x (adL l d)
      (by intro e; cases e)).2.2.2.2.1 (readers w) hd r j

/-- **THE CLAUSE ON DATA AT THE FIRST SEGMENT's FIRST THREE MESSAGES.** -/
theorem data_first_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {Qc : Par} (hQ : Qc.link = 0)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (S : Sz)
    {w : Local W₀ Rc ProofFile.Inst Tr} {heard : List Fmt.Drawn}
    {ca : CsAll (closeCarries ⟨Qc, borneAt Zp Qc⟩)} {a : Laid} {n nn fr : Nat} (hn : n < 3)
    (hfr : fr ≤ heard.length)
    (hL : LotMember readers (widerRows S Zp Bs.G₀) Zp Bs.G₀ Qc w heard ca n a nn) :
    a.1 = shapeAt parGF n ∧
      a.2 = fun r j => asRow ((shapeAt parGF n).mainDeg == 3)
        ((K1.lotData S Zp Bs.G₀ w.x).at_ (readers w) (heard.take fr) ⟨K1.firstAddr, n⟩ r j) := by
  obtain ⟨g1, g2, g3, -⟩ := lot_shape h O (l := 0) (by decide) hQ
  have hOne : (lotSegs Zp Bs.G₀ Qc).dropLast = [] := by
    rw [lot_front (segments_at_head h.toAtMg O) hQ (by decide)]
    rfl
  have t := dataFirst_written
  unfold dataFirstB at t
  obtain ⟨Sg, hSg⟩ : ∃ Sg, segsW[0]? = some Sg := by
    cases e : segsW[0]? with
    | none =>
      rw [e] at t
      cases t
    | some Sg => exact ⟨Sg, rfl⟩
  rw [hSg, Option.any_some, Bool.and_eq_true] at t
  obtain ⟨t1, t2⟩ := t
  have t3 := List.all_eq_true.1 t2 n (List.mem_range.2 hn)
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_zero] at t3
  obtain ⟨⟨u1, u2⟩, u3⟩ := t3
  refine data_first (D' := K1.lotData S Zp Bs.G₀ w.x) (g1.trans hSg) hOne
    (by rw [of_decide_eq_true t1]; exact hn) hL ?_ ?_ ?_ ?_
    (by rw [heardAt_first]; exact Nat.zero_le _) hfr
  · intro o ho
    rw [ho] at u1
    exact Option.some.inj u1
  · rw [g2, addrs_at_head h O]
    exact u2
  · rw [g2, g3, hSg]
    exact u3
  · intro hd r j
    exact (with_other_kind S (K1.lotData S) Zp Bs.G₀ w.x ⟨K1.firstAddr, n⟩
      (by intro e; cases e)).2.2.2.2.1 (readers w) hd r j

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.dataLater_written
#print axioms ProofFile.Honest.K10.dataLater_bent
#print axioms ProofFile.Honest.K10.dataHeard_written
#print axioms ProofFile.Honest.K10.dataHeard_bent
#print axioms ProofFile.Honest.K10.dataFirst_written
#print axioms ProofFile.Honest.K10.dataFirst_bent
#print axioms ProofFile.Honest.K10.lotData_heardAt
#print axioms ProofFile.Honest.K10.heardAt_first
#print axioms ProofFile.Honest.K10.heardAt_later
#print axioms ProofFile.Honest.K10.lot_shape
#print axioms ProofFile.Honest.K10.data_later_head
#print axioms ProofFile.Honest.K10.data_first_head
