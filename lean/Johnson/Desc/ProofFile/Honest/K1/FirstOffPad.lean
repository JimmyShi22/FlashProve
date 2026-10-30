-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/FirstOffPad.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: "OFF THE PAD" AT THE FIRST SEGMENT's OPENING, IN THE SENDER's OWN LETTERS:
at codes whose lengths are powers of two, where the opening's filling firstFill
(Honest/K1/PlaceFirst.lean) lays an element at message number k, row r, place j: the row and the
place lie inside the message's main table AT THE PLAN's OWN SHAPE shapeAt (K1.firstPar q gp) k, off
the places of its sample's pad, and the message is sampled. Statements and proofs on public data; no
definition.

  first_lays_seat   tool: where firstFill lays, the address has a seat
  first_lays_room   THE JOIN: under "the codes' lengths are powers of two": inside the rows · inside
                the code's length · not among padInMain's places · the message has an answer
  first_lays_off_padB   the same in the form of the library's plain test padB
  first_clear   the seat's own test RowData.clear holds at every seated message of the opening,
                under the same premise on the lengths
  first_lays_room_pub   AT A MADE PUBLIC PART the premise on the lengths is paid: no premise is left
                but that ProofFile.pureRoad.pub returns. IT ENDS IN LESS THAN THE JOIN: inside the rows ·
                inside the code's length · off padB's places: not padInMain's form, and not that the
                message has an answer

It joins two files: lays_room, lays_off_padB, clear_laid, msgFits_pub (Honest/Law/LaysRoom.lean,
LaysRoomPub.lean: at the shape IN THE REQUEST's LIST) and first_seat_shape
(Honest/K1/SeatShape.lean: that shape is the sender's).

Limits. THE OPENING's OWN MESSAGES ALONE: the arrays "M mu" of segment 0. Not the reads', not the
digits', not W's, not the switch's sendings. padB says of itself: at one answer. What a program lays
is not spoken of. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.SeatShape
import Johnson.Desc.ProofFile.Honest.Law.LaysRoomPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc
open OnBytes.HonestTrace (Sz)
open Johnson.Prover.Send (shapeAt)

theorem first_lays_seat (S : Sz) (q : Params.First) (k r j : Nat)
    (h : (firstFill S q).lays ⟨firstAddr, k⟩ r j = true) :
    ∃ l m, firstSeat q.shape 0 ⟨firstAddr, k⟩ = some (l, m) := by
  cases e : firstSeat q.shape 0 ⟨firstAddr, k⟩ with
  | some x => exact ⟨x.1, x.2, rfl⟩
  | none =>
    unfold firstFill firstData laidData at h
    simp only [e] at h
    cases h

/-- **THE JOIN.** -/
theorem first_lays_room (S : Sz) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (hlen : q.codes.lengthsOk = true) (k r j : Nat)
    (h : (firstFill S q).lays ⟨firstAddr, k⟩ r j = true) :
    r < (shapeAt (K1.firstPar q gp) k).mainRows ∧
      j < ((K1.firstPar q gp).codes.base.getD (shapeAt (K1.firstPar q gp) k).code default).ell ∧
      (r, j) ∉ padInMain
        ((K1.firstPar q gp).codes.base.getD (shapeAt (K1.firstPar q gp) k).code default).ell
        (shapeAt (K1.firstPar q gp) k) ∧
      (shapeAt (K1.firstPar q gp) k).answers ≠ 0 := by
  obtain ⟨l, m, hs⟩ := first_lays_seat S q k r j h
  obtain ⟨hl, M, hM, hsh⟩ := first_seat_shape q gp k l m hs
  subst hl
  rw [← hsh]
  exact lays_room q.codes q.shape q.layout (firstSeat q.shape 0) (fun _ => 0) (cellsVals S) hlen hs
    hM h

theorem first_lays_off_padB (S : Sz) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (hlen : q.codes.lengthsOk = true) (k r j : Nat)
    (h : (firstFill S q).lays ⟨firstAddr, k⟩ r j = true) :
    padB (K1.firstPar q gp).codes (shapeAt (K1.firstPar q gp) k) false r j = false := by
  obtain ⟨l, m, hs⟩ := first_lays_seat S q k r j h
  obtain ⟨hl, M, hM, hsh⟩ := first_seat_shape q gp k l m hs
  subst hl
  rw [← hsh]
  exact lays_off_padB q.codes q.shape q.layout (firstSeat q.shape 0) (fun _ => 0) (cellsVals S)
    hlen hs hM h

theorem first_clear (S : Sz) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (hlen : q.codes.lengthsOk = true) (k l m : Nat)
    (hs : firstSeat q.shape 0 ⟨firstAddr, k⟩ = some (l, m)) :
    (firstFill S q).clear ⟨firstAddr, k⟩
      (q.codes.base.getD (shapeAt (K1.firstPar q gp) k).code default).ell
      (shapeAt (K1.firstPar q gp) k) = true := by
  obtain ⟨hl, M, hM, hsh⟩ := first_seat_shape q gp k l m hs
  subst hl
  rw [← hsh]
  exact clear_laid q.codes q.shape q.layout (firstSeat q.shape 0) (fun _ => 0) (cellsVals S) hlen
    hs hM

/-- **At a made public part.** -/
theorem first_lays_room_pub {o : ProofFile.SecondHashFunctionArgument} {pol ly KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol ly KL = .ok Z) (S : Sz) (gp : _root_.Desc.Plain.GPar)
    (k r j : Nat) (h : (firstFill S Z.first).lays ⟨firstAddr, k⟩ r j = true) :
    r < (shapeAt (K1.firstPar Z.first gp) k).mainRows ∧
      j < ((K1.firstPar Z.first gp).codes.base.getD
        (shapeAt (K1.firstPar Z.first gp) k).code default).ell ∧
      padB (K1.firstPar Z.first gp).codes (shapeAt (K1.firstPar Z.first gp) k) false r j =
        false := by
  obtain ⟨l, m, hs⟩ := first_lays_seat S Z.first k r j h
  obtain ⟨hl, M, hM, _⟩ := first_seat_shape Z.first gp k l m hs
  subst hl
  have hlen : Z.first.codes.lengthsOk = true :=
    (msgFits_pub hZ (List.getElem?_eq_some_iff.1 hM).1).2
  have h1 := first_lays_room S Z.first gp hlen k r j h
  exact ⟨h1.1, h1.2.1, first_lays_off_padB S Z.first gp hlen k r j h⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.first_lays_seat
#print axioms ProofFile.Honest.K1.first_lays_room
#print axioms ProofFile.Honest.K1.first_lays_off_padB
#print axioms ProofFile.Honest.K1.first_clear
#print axioms ProofFile.Honest.K1.first_lays_room_pub
