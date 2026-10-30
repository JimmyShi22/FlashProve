-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/MaskStartIsBook.lean: THE SHARED "SENDING" (the kind K1) AND
THE MAKER OF THE BOOK OF COINS: TWO TEXTS OF ONE NUMBER: WHERE THE ENTRIES OF A MESSAGE's MASK ROWS
BEGIN AMONG THE SENDING's COINS: the maker's maskStart
(Johnson/Desc/ProofFile/Honest/BookRows.lean) AGAINST OUR maskStart
(Johnson/Desc/ProofFile/Honest/K1/MaskLaw.lean), AT EVERY MESSAGE OF EVERY PLAN. PUBLIC DATA ALONE:
numbers of coins; never what a coin is. Three theorems; NO DEFINITION. A TRIAL THAT COUNTS IN NO
COLUMN.
NO PROPERTY IS CLAIMED.

WHY. Two files name this as what no lemma says:
Johnson/Desc/ProofFile/Honest/Law/Rule/TiesOwn.lean: "a further sentence, on closed numbers, which
a test with code is to print; no lemma says it"; AtFullSide/K14/RawK3Fits.lean: "A BOOK's NUMBER IS
A CLAIM ON A SENDER's TEXT". The road:
DueIsBook.lean's sendDue_start and msgDue_steps: the maker's maskStart looks joinable to
them by a short law at all five messages and every plan.

UNDER THE TWO PUBLIC PREMISES OF Johnson/Desc/ProofFile/Honest/K1/Law/DueIsBook.lean: hf: our test
sendFits · ht: THE TIE OF THE RIDE: a table rides just at the messages that the maker's test
isFresh accepts, and at the maker's k.
  - maskStart_book   THE MAKER's maskStart AT P.codes, k, P.sent.toList, j RETURNS: startR P ride
                  j, plus what stands in front of the mask rows' entries in message j, by field.
  - maskStart_book_e   ITS COUNT OF THE EXTENSION FIELD IS OUR maskStart P ride j.
  - maskStart_book_next   A NUMBER THAT IS NOT THE START: behind message j's mask entries and their
                  tails the next message's coins of the extension field begin: (startR P ride (j +
                  1)).e = maskStart P ride j + the entries + the tails.

BY WHAT: sendDue_start · msgDue_steps · sentList_at (DueIsBook.lean) · startR_succ (MaskLaw.lean) ·
fits_shape (Johnson/Desc/ProofFile/Honest/K1/PadLaw.lean); the two texts. KIN: start_e
(Johnson/Desc/ProofFile/Honest/K1/Seat.lean) has the next message's start by dueMsg;
maskStart_book_next has it by maskStart, the entries and the tails; another house's own_end
(Johnson/SendSim/At/GuardTestTie.lean) has the inequality without the tails.

Limits. IT SAYS NOTHING OF ownerOf: that the sending which the maker finds under a label has P.sent
and P.codes, that its k (foldK) is the fold's own, and which message its search picks: closed
numbers at written data: not here. Nothing on the book's entries. hf AND ht ARE PREMISES. It stands
over a file that is in no seal and on no row (DueIsBook.lean). Nothing on what any coin is. Nothing
on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.DueIsBook
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.K1.PadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- **THE MAKER's COUNT RETURNS, AND IS OURS, BY FIELD.** -/
theorem maskStart_book (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (hf : sendFits P ride = true)
    (ht : ∀ j, j < P.sent.size →
      (ride j).map (·.k) = if isFresh (P.sent.getD j default) then some k else none)
    {j : Nat} (hj : j < P.sent.size) :
    _root_.ProofFile.Honest.maskStart P.codes k P.sent.toList j =
      some ((startR P ride j).plus
        (if (shapeAt P j).mainDeg == 1 then
          ⟨(stepsOf P.codes (shapeAt P j) (ride j)).main, 0⟩
        else ⟨0, (stepsOf P.codes (shapeAt P j) (ride j)).main⟩)) := by
  unfold _root_.ProofFile.Honest.maskStart
  rw [sendDue_start P ride k hf ht j (Nat.le_of_lt hj), sentList_at P hj]
  show ((msgDue P.codes k (P.sent.getD j default)).map fun d =>
    (startR P ride j).plus d.main) = _
  rw [msgDue_steps P.codes k _ (ride j) (fits_shape P ride j hf hj) (ht j hj)]
  rfl

/-- **THE MAKER's COUNT OF THE EXTENSION FIELD IS OUR maskStart.** -/
theorem maskStart_book_e (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (hf : sendFits P ride = true)
    (ht : ∀ j, j < P.sent.size →
      (ride j).map (·.k) = if isFresh (P.sent.getD j default) then some k else none)
    {j : Nat} (hj : j < P.sent.size) :
    (_root_.ProofFile.Honest.maskStart P.codes k P.sent.toList j).map (·.e) =
      some (maskStart P ride j) := by
  rw [maskStart_book P ride k hf ht hj, Option.map_some]
  have hs := fits_shape P ride j hf hj
  simp only [Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
  have h4 : (shapeAt P j).mainDeg = 1 ∨ (shapeAt P j).mainDeg = 3 := hs.2
  rcases h4 with h4 | h4 <;> simp [maskStart, h4]

/-- **BEHIND THE MASK ENTRIES AND THEIR TAILS THE NEXT MESSAGE BEGINS.** No premise. -/
theorem maskStart_book_next (P : K1.Par) (ride : Nat → Option Ride) (j : Nat) :
    (startR P ride (j + 1)).e = maskStart P ride j +
      (stepsOf P.codes (shapeAt P j) (ride j)).mask +
      (stepsOf P.codes (shapeAt P j) (ride j)).maskTails := by
  rw [startR_succ]
  unfold maskStart dueMsg
  by_cases h : (shapeAt P j).mainDeg == 3 <;> simp [h, Nat.add_assoc]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.maskStart_book
#print axioms ProofFile.Honest.K1.maskStart_book_e
#print axioms ProofFile.Honest.K1.maskStart_book_next
