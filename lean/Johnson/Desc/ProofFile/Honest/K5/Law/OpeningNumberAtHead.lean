-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OpeningNumberAtHead.lean: conditional, under the library's head:
which number of the witness's messages a message of the opening has that is seated at segment 0. A
message number n of the first segment's opening that `K1.firstSeat` seats at (0, m') is one of the
opening's plan's messages, and the numbering `P5J.At.arr Zp` at its seat at member number 2 of the
first chain is `P5J.At.num Zp 0 m'`. Public data alone: plans, the plan's list of seats, numbers. No
definition; five theorems.

  `openingKeysW`         at the written plan: wherever `msgNo` answers m' at message n of the opening,
                         the first written seat found at that message's seat has the key (0, 0, m')
  `openingKeysW_bites`   a negative test: with the key (0, 0, m' + 1) in the place of (0, 0, m') the same
                         test says no
  `openingCountW`        at the written shape segment 0 has no more messages of moment 0 than the
                         opening's written plan has messages
  `openingSeatedW`       not of nothing: `msgNo` answers at three of the opening's five messages
  `opening_number_head`  the law, under the head h and the opened description O

What it is for. The attention sub-protocol reads arrays of segment 0 out of the opening's messages
by the number `P5J.At.num Zp 0 m'`; the lots of the shared sending bear the number `P5J.At.arr Zp` at
the message's seat (`K1.k1Num`, Honest/K1/Law/K1NumAtHead.lean). This file says that the two are one
number. It is the sister, at the opening, of `K1.k1Num_fifty` in that file.

How. Under the head the shape is the written one (`H2K5.Door.pins_at_head`), the opening's plan is the
written one (`K1.eG_atAll`), our seat is the written plan's (`K1.seat_two_written`) and the plan's list
of seats is the written list (`K1.pseatsAll_written`). At these constants the facts are closed and are
evaluated in Lean's kernel. Then `P5T.arrOf_is_num` (Johnson/P5T/NumOfPlan.lean).

Limits. The full size alone. Which message, never what stands in it. The plan is the description's
ground's. Evaluations in Lean's kernel (decide +kernel): no compiled code. At the earlier hash
`OnBytes.secondHashFunction`, a fixed function. This file proves nothing about soundness, completeness, hiding or
any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF seatOfMsg)
open VerifiableInference.PlanWritten (proofSizedFull)
open P5T (PSeat seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 At the written plan -/

/-- At the written plan: wherever `msgNo` answers m' at message n of the opening, the written list of
seats has a seat at that message's seat, and its key is (0, 0, m'). -/
theorem openingKeysW : ((List.range parGF.sent.size).all fun n =>
    (msgNo proofSizedFull.request 0 0 n).all fun m' =>
      (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2).any fun p => decide (keyOf p = (0, 0, m'))) = true := by
  decide +kernel

/-- A negative test: with the key (0, 0, m' + 1) in the place of (0, 0, m') the same test says no. -/
theorem openingKeysW_bites : ((List.range parGF.sent.size).all fun n =>
    (msgNo proofSizedFull.request 0 0 n).all fun m' =>
      (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 n).1 &&
        p.t == (seatOfMsg parGF 0 n).2).any fun p => decide (keyOf p = (0, 0, m' + 1))) = false := by
  decide +kernel

/-- At the written shape segment 0 has no more messages of moment 0 than the opening's written plan
has messages. -/
theorem openingCountW :
    ((proofSizedFull.request.link.getD 0 default).messages.zipIdx.filter
      fun m => m.1.moment == 0).length ≤ parGF.sent.size := by
  decide +kernel

/-- Not of nothing: `msgNo` answers at three of the opening's five messages. -/
theorem openingSeatedW : (List.range parGF.sent.size).map
    (fun n => msgNo proofSizedFull.request 0 0 n) =
    [some 0, some 1, some 2, none, none] := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **A message of the opening that is seated at (0, m') is one of the plan's messages, and its
number in the witness is `P5J.At.num Zp 0 m'`.** Conditional: h, the library's head; O, the
description opened; hAd. -/
theorem opening_number_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {n m' : ℕ}
    (hAd : ProofFile.Honest.K1.firstSeat h.𝔇.sent.shape 0 ⟨ProofFile.Honest.K1.firstAddr, n⟩ = some (0, m')) :
    n < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size ∧
      P5J.At.arr Zp (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).1
        (ProofFile.Honest.K1.seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) n).2 =
        P5J.At.num Zp 0 m' := by
  have hm := (H2K5.Door.pins_at_head h.toAtMg).1
  obtain ⟨-, -, f3, -, -, -⟩ := (H2K5.Door.made_row_gives hm).1
  have es : h.𝔇.sent.shape = proofSizedFull.request := f3
  rw [es] at hAd
  have hno : msgNo proofSizedFull.request 0 0 n = some m' := by
    unfold ProofFile.Honest.K1.firstSeat ProofFile.Honest.K1.momentSeat at hAd
    split at hAd
    · obtain ⟨m₀, e, hp⟩ := Option.map_eq_some_iff.1 hAd
      have h2 : m₀ = m' := congrArg Prod.snd hp
      subst h2
      exact e
    · cases hAd
  have hnW : n < parGF.sent.size := by
    unfold msgNo at hno
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hno
    exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hy).1 openingCountW
  have eP : (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) = parGF := K1.eG_atAll h O (K1.pin1_atAll h)
  refine ⟨by rw [eP]; exact hnW, ?_⟩
  have t := List.all_eq_true.1 openingKeysW n (List.mem_range.2 hnW)
  rw [hno, Option.all_some] at t
  rw [ProofFile.Honest.K1.seat_two_written h O n]
  cases hf : seatsAllFull.find? (fun p => p.j == (seatOfMsg parGF 0 n).1 &&
      p.t == (seatOfMsg parGF 0 n).2) with
  | none =>
    rw [hf] at t
    cases t
  | some p =>
    rw [hf, Option.any_some] at t
    exact P5T.arrOf_is_num _ _ _ 0 m' p
      (by rw [ProofFile.Honest.K1.pseatsAll_written h]; exact hf) (of_decide_eq_true t)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.openingKeysW
#print axioms ProofFile.Honest.K5.openingKeysW_bites
#print axioms ProofFile.Honest.K5.openingCountW
#print axioms ProofFile.Honest.K5.openingSeatedW
#print axioms ProofFile.Honest.K5.opening_number_head
