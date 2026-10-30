-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnStand.lean: at the border in front of the closing of a segment: the list of challenges heard fits the first declared rounds
and reaches the sending of every own message of the segments up to that one. So the digits' data are ready there, where the
public data fit.

  `fit_length`, `heard_fits_front`   a list that fits the rounds in front of a border is as long as the written count of these
                     rounds, and fits the public part's first declared rounds
  `seatFrontB`, `seatSegB`   two tests on the written seats of an array's name: each seat's sending begins in front of its
                     segment's closing · the seat at the address of an own message of segment j is segment j's
  `seatFront_bz`, `seatFront_u3`, `seatSeg_bz`, `seatSeg_u3`   they say yes at "BZ" and at "U3": by Lean's kernel; with controls
  `roundsW_mono`      the written count of rounds in front of a border grows with the border
  `addrs_at_head`     under the head the closing's reader of addresses is the written one
  `own_seat_le`       so: a seat at the address of an own message of the segments up to l has been reached at closing l
  **`digits_at_stand`**   the premise on the digits' filling of `ownHeard_of_two` (MadeOwnAB.lean), from `DigitsFit`

Limits. `DigitsFit` at the addresses of the digits' share is a premise. The head and the opening are hypotheses. The full size
and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnDigits
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeOwnAB
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeStand
import Johnson.Desc.ProofFile.Honest.K2.Law.LightWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.LightByAddress
import Johnson.HonestTrace.U3Fit.SeatsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.PlanWritten (cutFirstFull)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Seat seatsOf seatAt)
open OnBytes.HonestTrace.U3.Fit (seatsW seats_at_head)
open ProofFile.Honest.K2 (segmentsOf mineDigits)
open ProofFile.Honest.K2.Law (segsW addrsW zipIdx_take_mem segments_at_head prep_at_head spots_at_head)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 The list heard -/

theorem fit_length : ∀ {ds : List Fmt.DeclaredRound} {hs : List Fmt.Drawn},
    drawsFit ds hs = true → hs.length = ds.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | d :: ds, R :: hs, h => by
    have h' : (drawFit d R && drawsFit ds hs) = true := h
    have e := fit_length (Eq.mp (Bool.and_eq_true _ _) h').2
    rw [List.length_cons, List.length_cons, e]

/-! ## 2 The written seats -/

/-- Each written seat of the name is a segment's below 25, and its sending begins in front of that
segment's closing. -/
def seatFrontB (name : String) : Bool :=
  (seatsW name).all fun t =>
    decide (t.seg < 25) && decide (t.heard ≤ roundsW (14 * t.seg + IM.nAt t.seg + 5))

/-- The written seat at the address of an own message of segment j is segment j's. -/
def seatSegB (name : String) : Bool :=
  segsW.zipIdx.all fun y => (y.1.ownShapes (y.2 == 0)).zipIdx.all fun s =>
    (addrsW y.2 s.2).all fun a => (seatAt (seatsW name) a).all fun t => t.seg == y.2

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem seatFront_bz : seatFrontB "BZ" = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem seatFront_u3 : seatFrontB "U3" = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: at the border in front of the segment's first sub-protocol no seat's sending has begun. -/
theorem seatFront_bite : (((seatsW "BZ").any fun t => decide (t.heard ≤ roundsW (14 * t.seg + 2))) ||
    (seatsW "U3").any fun t => decide (t.heard ≤ roundsW (14 * t.seg + 2))) = false := by
  decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem seatSeg_bz : seatSegB "BZ" = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem seatSeg_u3 : seatSegB "U3" = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- A control: the test asks something: some own message's address is a seat's, at each name. -/
theorem seatSeg_bite : ((segsW.zipIdx.any fun y => (y.1.ownShapes (y.2 == 0)).zipIdx.any fun s =>
      (addrsW y.2 s.2).any fun a => (seatAt (seatsW "BZ") a).isSome) &&
    (segsW.zipIdx.any fun y => (y.1.ownShapes (y.2 == 0)).zipIdx.any fun s =>
      (addrsW y.2 s.2).any fun a => (seatAt (seatsW "U3") a).isSome)) = true := by
  decide +kernel

theorem sum_take_mono : ∀ (l : List Nat) (a b : Nat), a ≤ b → (l.take a).sum ≤ (l.take b).sum
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => by simp
  | _ :: _, _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | x :: l, a + 1, b + 1, h => by
    rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_take_mono l a b (Nat.le_of_succ_le_succ h)) x

theorem roundsW_mono {a b : Nat} (h : a ≤ b) : roundsW a ≤ roundsW b := by
  unfold roundsW
  rw [List.map_take, List.map_take]
  exact sum_take_mono _ a b h

theorem closing_mono {j l : Nat} (h : j ≤ l) :
    14 * j + IM.nAt j + 5 ≤ 14 * l + IM.nAt l + 5 := by
  unfold IM.nAt
  split <;> split <;> omega

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- A list that fits the rounds in front of a border. -/
theorem heard_fits_front (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {b : Nat}
    {heard : List Fmt.Drawn} (hd : drawsFit (declsTo cF.blocksInOrder b) heard = true) :
    heard.length = roundsW b ∧ drawsFit (Zp.D.1.take heard.length) heard = true := by
  obtain ⟨eT, eL⟩ := declared_in_front h b
  have hl := fit_length hd
  refine ⟨hl.trans eL, ?_⟩
  rw [hl, ← eT]
  exact hd

/-- Under the head the closing's reader of addresses is the written one. -/
theorem addrs_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : addrsAt Zp Bs.G₀ = addrsW := by
  unfold addrsAt addrsW
  rw [prep_at_head h.toAtMg O, spots_at_head h.toAtMg O]
  cases IM.prepW <;> rfl

/-- **A seat at the address of an own message of the segments up to l has been reached at closing
l.** -/
theorem own_seat_le (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (_hl : l < 25) {Qc : Par} (hQ : Qc.link = l)
    {name : String} (hA : seatFrontB name = true) (hB : seatSegB name = true) {a : MsgAddr}
    (ha : OwnAddr (addrsAt Zp Bs.G₀) (lotSegs Zp Bs.G₀ Qc) a) {t : Seat}
    (ht : seatAt (seatsOf Zp Bs.G₀ name) a = some t) :
    t.heard ≤ roundsW (14 * l + IM.nAt l + 5) := by
  rw [seats_at_head h O.blank name] at ht
  obtain ⟨y, hy, s, hs, e⟩ := ha
  have eS : lotSegs Zp Bs.G₀ Qc = segsW.take (l + 1) := by
    show (segmentsOf Zp Bs.G₀).take (Qc.link + 1) = _
    rw [segments_at_head h.toAtMg O, hQ]
  rw [eS] at hy
  have hyW := zipIdx_take_mem segsW (l + 1) hy
  have hyl : y.2 < l + 1 := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_take] at hy
    split at hy
    · assumption
    · cases hy
  rw [addrs_at_head h O] at e
  have t1 := List.all_eq_true.1 (List.all_eq_true.1 hB y hyW) s hs
  rw [e, Option.all_some, ht, Option.all_some] at t1
  have e1 : t.seg = y.2 := beq_iff_eq.1 t1
  have t2 := List.all_eq_true.1 hA t (List.mem_of_find?_eq_some ht)
  obtain ⟨-, t3⟩ := Eq.mp (Bool.and_eq_true _ _) t2
  exact Nat.le_trans (of_decide_eq_true t3)
    (roundsW_mono (closing_mono (by omega)))

/-- **THE DIGITS' DATA ARE READY IN FRONT OF A CLOSING**, where the public data fit. -/
theorem digits_at_stand (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : Nat} (hl : l < 25) {Qc : Par} (hQ : Qc.link = l)
    (F : ∀ a, mineDigits Zp Bs.G₀ a = true → DigitsFit Zp Bs.G₀ (K3.matsOwn Bs.G₀.W) a)
    {heard : List Fmt.Drawn}
    (hd : drawsFit (declsTo cF.blocksInOrder (14 * l + IM.nAt l + 5)) heard = true) :
    ∀ a, OwnAddr (addrsAt Zp Bs.G₀) (lotSegs Zp Bs.G₀ Qc) a → mineDigits Zp Bs.G₀ a = true →
      (K1.digitsFill Zp Bs.G₀ (K3.matsOwn Bs.G₀.W)).readyAt heard a = true := by
  intro a ha hm
  obtain ⟨e1, e2⟩ := heard_fits_front h hd
  refine digits_ready (F a hm) e2 fun s hs => ?_
  rw [e1]
  exact own_seat_le h O hl hQ seatFront_bz seatSeg_bz ha hs

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.fit_length
#print axioms ProofFile.Honest.K10.seatFront_bz
#print axioms ProofFile.Honest.K10.seatFront_u3
#print axioms ProofFile.Honest.K10.seatFront_bite
#print axioms ProofFile.Honest.K10.seatSeg_bz
#print axioms ProofFile.Honest.K10.seatSeg_u3
#print axioms ProofFile.Honest.K10.seatSeg_bite
#print axioms ProofFile.Honest.K10.sum_take_mono
#print axioms ProofFile.Honest.K10.roundsW_mono
#print axioms ProofFile.Honest.K10.closing_mono
#print axioms ProofFile.Honest.K10.heard_fits_front
#print axioms ProofFile.Honest.K10.addrs_at_head
#print axioms ProofFile.Honest.K10.own_seat_le
#print axioms ProofFile.Honest.K10.digits_at_stand
