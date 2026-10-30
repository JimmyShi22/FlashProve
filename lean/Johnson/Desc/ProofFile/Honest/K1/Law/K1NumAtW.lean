-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/K1NumAtW.lean: THE SHARED "SENDING" (the kind K1): WHICH NUMBER
OF THE WITNESS's MESSAGES, AND WHICH SEAT OF THE PLAN's OWN LIST, MESSAGE NUMBER n OF W's SENDING
(number 356 of the first chain) HAS, UNDER THE LIBRARY's HEAD: the like of K1NumAtHead.lean, whose
51 places lack this one. PUBLIC DATA ALONE: plans, the plan's list of seats, numbers: which message,
never what stands in it. Eleven theorems; no definition (k1Num, k1SeatIn: K1NumAtHead.lean).


The road is K1NumAtHead.lean's. Under the head the plan's list of all three chains' seats is the
library's written seatsAllFull (pseatsAll_written), and our seat is the written plan's behind 82
trees (seat_w_written: nums_w, SeatsAtW.lean; parW_written, FitsAtW.lean). At these constants all is
closed facts, evaluated in Lean's kernel.

  - seatW356: AT BOTH MESSAGES OF THE PLAN, SAMPLED OR NOT: the written list filtered at our seat is
    ONE seat: member number n of sending number 81, of the message's shape. backW356: the other way:
    the list filtered at (sending 81, place n) is one seat, and it is ours. keysW356: the two keys:
    (1, 81, 0), (1, 81, 1): by sending and place: no link's own message. It says the keys alone.
    wSeatW356: number 0 alone sits at the written numbers' w.
  - seatW356_bites: A NEGATIVE TEST: one tree further the test says no at each message.
  - seat_w, seatIn_w: UNDER h (the library's head: A HYPOTHESIS), O (the description opened), n
    below the plan's number of messages: JUST ONE SEAT p OF P5J.At.pseatsAll Zp STANDS AT OUR SEAT,
    with p.send = 81, p.idx = n, p.shape; and THE TWO READINGS ARE ONE.
  - k1Num_w_key: so k1Num there is the place of that seat's key among the keys: it does not fall
    "beyond the list" (k1Num_of_one).
  - w_at_zero, k1Num_w_zero: MESSAGE NUMBER 0 SITS AT THE TABLE's N.w: so k1Num there is P5J.At.arr
    Zp N.w.1 N.w.2.

Limits. THE FULL SIZE ALONE. THE PLAN IS THE DESCRIPTION's PUBLIC PART's: that it is the plan of the
prover that a filling makes is another file's. Nothing is said of the Script: that its message at
this number is our text is the record's field msgs: a premise. That these two numbers part from the
numbers at the 51 places is not said here. Evaluations in Lean's kernel (decide +kernel): no
compiled code. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (parWF seatOfMsg)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open P5T (PSeat N0Full seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)

/-! ## 1 At the written constants -/

/-- AT W's SENDING's WRITTEN PLAN, AT BOTH MESSAGES, SAMPLED OR NOT: the written list of all three
chains' seats has just one seat at our seat: member number n of sending number 81, of the message's
shape. -/
theorem seatW356 : ((List.range parWF.sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.j == (seatOfMsg parWF 82 n).1 &&
        p.t == (seatOfMsg parWF 82 n).2).length = 1) &&
      (seatsAllFull.filter fun p => p.j == (seatOfMsg parWF 82 n).1 &&
        p.t == (seatOfMsg parWF 82 n).2).all fun p =>
          p.send == 81 && p.idx == n && decide (p.shape = shapeAt parWF n)) = true := by
  decide +kernel

/-- The other way: the list has just one member number n of sending number 81, and it sits at our
seat. -/
theorem backW356 : ((List.range parWF.sent.size).all fun n =>
    decide ((seatsAllFull.filter fun p => p.send == 81 && p.idx == n).length = 1) &&
      (seatsAllFull.filter fun p => p.send == 81 && p.idx == n).all fun p =>
        decide ((p.j, p.t) = seatOfMsg parWF 82 n)) = true := by
  decide +kernel

/-- The keys at W's sending: both by sending and place. -/
theorem keysW356 : (List.range parWF.sent.size).map (fun n =>
    (seatsAllFull.find? fun p => p.j == (seatOfMsg parWF 82 n).1 &&
      p.t == (seatOfMsg parWF 82 n).2).map keyOf) = [some (1, 81, 0), some (1, 81, 1)] := by
  decide +kernel

/-- The one message of W's sending whose seat is the written numbers' w is number 0. -/
theorem wSeatW356 : (List.range parWF.sent.size).filter
    (fun n => decide (seatOfMsg parWF 82 n = N0Full.w)) = [0] := by
  decide +kernel

/-- A negative test: one tree further, at EACH message the test says no. -/
theorem seatW356_bites : ((List.range parWF.sent.size).all fun n =>
    !(decide ((seatsAllFull.filter fun p => p.j == (seatOfMsg parWF 83 n).1 &&
        p.t == (seatOfMsg parWF 83 n).2).length = 1) &&
      (seatsAllFull.filter fun p => p.j == (seatOfMsg parWF 83 n).1 &&
        p.t == (seatOfMsg parWF 83 n).2).all fun p =>
          p.send == 81 && p.idx == n && decide (p.shape = shapeAt parWF n))) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- Our seat at number 356 is the written plan's, behind 82 trees. -/
theorem seat_w_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (n : ℕ) :
    seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n = seatOfMsg parWF 82 n := by
  unfold seatAtMember
  rw [(nums_w h O).2, parW_written h O]

/-- **AT NUMBER 356, AT BOTH MESSAGES OF THE PLAN, SAMPLED OR NOT: JUST ONE SEAT OF THE PLAN's LIST
STANDS AT OUR SEAT**: member number n of sending number 81, of the message's shape. -/
theorem seat_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) :
    ∃ p, ((P5J.At.pseatsAll Zp).filter fun p =>
        p.j == (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).1 &&
          p.t == (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n).2) = [p] ∧
      p.send = 81 ∧ p.idx = n ∧ p.shape = shapeAt (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n := by
  rw [seat_w_written h O n, pseatsAll_written h]
  rw [parW_written h O] at hn ⊢
  obtain ⟨p, e, hp⟩ := one_of_test (List.all_eq_true.1 seatW356 n (List.mem_range.2 hn))
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, decide_eq_true_eq] at hp
  exact ⟨p, e, hp.1.1, hp.1.2, hp.2⟩

/-- **THE OTHER READING AT NUMBER 356**: the seat read off the plan's list, by the sending and the
member's place in it, is our seat. -/
theorem seatIn_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) :
    k1SeatIn (P5J.At.pseatsAll Zp) 81 n =
      some (seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n) := by
  rw [seat_w_written h O n, pseatsAll_written h]
  rw [parW_written h O] at hn
  obtain ⟨p, e, hp⟩ := one_of_test (List.all_eq_true.1 backW356 n (List.mem_range.2 hn))
  unfold k1SeatIn
  rw [(one_of_filter e).2.2.2, Option.map_some, of_decide_eq_true hp]

/-- **THE NUMBER DOES NOT FALL BEYOND THE LIST**: it is the place, among the keys, of the key of a
seat of sending number 81. -/
theorem k1Num_w_key (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n : ℕ}
    (hn : n < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size) :
    ∃ p : PSeat, p.send = 81 ∧ p.idx = n ∧
      k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) n =
        (((P5J.At.pseatsAll Zp).map keyOf).eraseDups).idxOf (keyOf p) := by
  obtain ⟨p, e, h1, h2, -⟩ := seat_w h O hn
  exact ⟨p, h1, h2, k1Num_of_one e⟩

/-- **MESSAGE NUMBER 0 SITS AT THE TABLE's SEAT OF W.** -/
theorem w_at_zero (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 0 = (P5J.At.N Zp cF).w := by
  rw [seat_w_written h O 0]
  have e : (P5J.At.N Zp cF).w = N0Full.w :=
    congrArg (·.w) (K1.atAll_letters h O (K1.pin1_atAll h)).1
  rw [e]
  have hm : 0 ∈ (List.range parWF.sent.size).filter
      (fun n => decide (seatOfMsg parWF 82 n = N0Full.w)) := by
    rw [wSeatW356]
    exact List.mem_singleton.2 rfl
  exact of_decide_eq_true (List.mem_filter.1 hm).2

/-- So the number there is the table's number at that seat. -/
theorem k1Num_w_zero (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    k1Num Zp cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) 0 =
      P5J.At.arr Zp (P5J.At.N Zp cF).w.1 (P5J.At.N Zp cF).w.2 := by
  unfold k1Num
  rw [w_at_zero h O]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.seatW356
#print axioms ProofFile.Honest.K1.backW356
#print axioms ProofFile.Honest.K1.keysW356
#print axioms ProofFile.Honest.K1.wSeatW356
#print axioms ProofFile.Honest.K1.seatW356_bites
#print axioms ProofFile.Honest.K1.seat_w_written
#print axioms ProofFile.Honest.K1.seat_w
#print axioms ProofFile.Honest.K1.seatIn_w
#print axioms ProofFile.Honest.K1.k1Num_w_key
#print axioms ProofFile.Honest.K1.w_at_zero
#print axioms ProofFile.Honest.K1.k1Num_w_zero
