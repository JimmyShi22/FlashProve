-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38J/AheadArms.lean: the two clauses of `DigAheadOk` that speak of a message which
is still ahead, at every seat of a cell of the digits' array.

Why. At each cell of its range `DigAheadOk` (Johnson/Desc/First/Look/K3DigitsAhead.lean) asks two
things of the reader `aheadIn` at the digits' array. Where it answers: its seat is the list's seat
of the cell's message, and the array's rectangles are lawful at the message's sizes. Where it is
silent: the message is sent, with four facts on it. Behind the approximate range proof's draw the
digits' message is not sent yet: the reader answers, and its value is known. So the first clause is
an equation of two seats, and the second is never met.

What is shown. General in all letters.
  `j_arms_of_msg`: both clauses at a seat z whose message is the array's.
  `ahead_arms`: **both clauses at every seat z that `seatOf` finds for a cell of the digits'
    array.** The cell's message is the array's by `seatOf_cell_parts`.

Premises: the list names the digits' array bn; the layout has it as A; `aheadIn` answers A, the seat
of A's message, and a shape; A's rectangles are lawful at that shape; the seats of the list are the
function seat.

Grade. General: no head is named.

Limits. The premises are shown here of no state. Nothing on soundness.


-/
import Johnson.Desc.First.Look.K3DigitsAhead
import Johnson.HB.LLHARD.Q38A.SeatOfCellParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (SeatOk)
open VerifiableInference.Desc.K9 (aheadIn rowBitsOf placeBitsOf)

/-- Both clauses at a seat whose message is the array's. -/
theorem j_arms_of_msg (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (N : Numbers) (l : ℕ)
    (a : VerifiableInference.Desc.K9.Part) (seat : ℕ → ℕ × ℕ) (hseat : ∀ k, seatT k = seat k.1)
    {bn : ℕ × String} {A : ReqArray} {sh : OracleShape}
    (hbn : (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn)
    (hah : aheadIn (N.sent l) (N.group l) a bn = some ⟨A, seat A.message, sh⟩)
    (hmat : laidMatrixOk A (rowBitsOf sh .main) (placeBitsOf D.codes sh .main) = true) {z : Seat}
    (hzm : z.msg = A.message) :
    (∀ bn h, (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
      aheadIn (N.sent l) (N.group l) a bn = some h →
      (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) =
          true) ∧
    (∀ bn a', (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
      aheadIn (N.sent l) (N.group l) a bn = none → reqArray D.layout bn.1 bn.2 = some a' →
      ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 (N.group l) a.d.st
          a.d.book z o ∧
        laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true) := by
  constructor
  · intro bn' h' e1 e2
    obtain rfl : bn = bn' := Option.some.inj (hbn.symm.trans e1)
    obtain rfl := Option.some.inj (hah.symm.trans e2)
    refine ⟨fun hk => ?_, hmat⟩
    rw [hseat]
    show seat A.message = seat z.msg
    rw [hzm]
  · intro bn' a' e1 e2 _
    obtain rfl : bn = bn' := Option.some.inj (hbn.symm.trans e1)
    rw [hah] at e2
    cases e2

/-- **Both clauses at every seat of a cell of the digits' array.** -/
theorem ahead_arms (x : Place) (tl : HTailF2) (D : Sent) (rad : OracleShape → ℕ)
    (seatT : Fin (digList x D rad).length → ℕ × ℕ) (N : Numbers) (l : ℕ)
    (a : VerifiableInference.Desc.K9.Part) (seat : ℕ → ℕ × ℕ) (hseat : ∀ k, seatT k = seat k.1)
    {bn : ℕ × String} {A : ReqArray} {sh : OracleShape}
    (hbn : (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn)
    (hA : reqArray D.layout x.link bn.2 = some A)
    (hah : aheadIn (N.sent l) (N.group l) a bn = some ⟨A, seat A.message, sh⟩)
    (hmat : laidMatrixOk A (rowBitsOf sh .main) (placeBitsOf D.codes sh .main) = true) {z : Seat}
    {u c : ℕ} (hz : seatOf D x.link (.cell tl.ix.ZZ u c) = some z) :
    (∀ bn h, (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
      aheadIn (N.sent l) (N.group l) a bn = some h →
      (∀ hk : z.msg < (digList x D rad).length, h.seat = seatT ⟨z.msg, hk⟩) ∧
        laidMatrixOk h.A (rowBitsOf h.shape .main) (placeBitsOf D.codes h.shape .main) =
          true) ∧
    (∀ bn a', (D.arrayOf.getD x.link #[])[tl.ix.ZZ]? = some bn →
      aheadIn (N.sent l) (N.group l) a bn = none → reqArray D.layout bn.1 bn.2 = some a' →
      ∃ o, SeatOk D.codes (digList x D rad) seatT a.L.check.frame 0 (N.group l) a.d.st
          a.d.book z o ∧
        laidMatrixOk a' (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true) := by
  obtain ⟨bn', A', rp, e1, -, e2, -, rfl⟩ := seatOf_cell_parts hz
  obtain rfl : bn = bn' := Option.some.inj (hbn.symm.trans e1)
  obtain rfl : A = A' := Option.some.inj (hA.symm.trans e2)
  exact j_arms_of_msg x tl D rad seatT N l a seat hseat hbn hah hmat rfl

end Q38

#print axioms Q38.j_arms_of_msg
#print axioms Q38.ahead_arms
