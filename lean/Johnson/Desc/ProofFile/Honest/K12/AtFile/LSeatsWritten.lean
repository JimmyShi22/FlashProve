-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LSeatsWritten.lean: a message's seat, read off the plan's
written lists; that a seat which the verifier's guard reads off its statement and book is the
written one, under three tests of the library on a reached state; and a closed line of Lean's kernel
on the two written seats in the tree that the first chain's closing proximity test opens.

  `writtenSeat`         the seat of message o by the lists: M, the messages' shapes; L, the
                        messages' (tree, part) and the trees' shapes
  `shape_of_seats`      of "the seats are carried": a tree of the book has the listed shape
  `writtenSeat_of_part` where the messages' shapes are the first of M, the seats are carried and the
                        book is in order from tree 0 on: a part of a tree (`Part1P`) is the written
                        seat
  `closingSeatsTest`    a test on the lists, the test's parameters q and the sender's place p: what
                        the argument of LSeatsLaw.lean spends
  `closingSeats_written`   THE CLOSED LINE: it says yes at the written values
  `closingSeats_written_no`   controls: 185 listed in tree 75 · a third message listed in tree 76 ·
                        the test's first tree is 1: it says no

The clauses of `closingSeatsTest`. (1) The test declares one opening, of tree number 76, counted
from its first tree, which is 0. (2) Of the listed messages none but 185 and 186 sits in tree 76.
(3) Both have a written seat, in tree 76; 185 has a main row, 186 has none. (4) At the layout that
`layTrees` returns at the sender's sending: the eight clauses of `FitsAtL` on the place; `SeatIs` at
0 for 185's seat and at 1 for 186's; and the clauses on rows, degree, depth and width, at these two
seats.

Limits.
- The numbers 76, 185 and 186 are written here. Were one wrong, the closed line would not compile.
- `writtenSeat` takes a tree's place in the list for its number: right for a chain whose first tree
  bears the number 0, as the first chain's does.
- The argument of LSeatsLaw.lean does not spend three clauses (186 has no main row; both sit in tree
  76). They stand as witnesses: without them the law could be empty.
- The full size alone: the library's written values.
- No state is named in the closed line.
- Nothing on completeness, on soundness or on hiding.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LShapeTest
import AtFullSide.K12.FitsAtHeadL
import Johnson.Desc.K12.Law.FirstOkLaw
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.P5J.ReadsTestsAtHead
import Johnson.Road.K4.K4PinsSends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (OracleShape TreeShape TreeBook Statement TreeLay layTrees)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.K12.Door (seatsCarriedB bookInOrderB msgShapesB msgShape_at
  place_of_seats numbers_of_book0)
open VerifiableInference.Desc.K13.Law (LFull)
open H2K.First (Seat1 kk)
open H2K.Sw (Part1P)

/-- The plan's lists of the messages' (tree, part) and of the trees' shapes. -/
local notation "Laid" => VerifiableInference.Desc.K12.Door.Laid
open H2K.Member (piLFull)
open ProofFile.Honest.K12 (stA)

/-- **The seat of message o by the plan's lists.** The tree's number is its place: the chain's first
tree has the number 0. -/
def writtenSeat (M : List OracleShape) (L : Laid) (o : ℕ) : Option Seat1 :=
  (M[o]?).bind fun sh => (L.places[o]?).bind fun q => (L.shapes[q.1]?).map fun tsh =>
    ⟨o, sh, q.1, q.2, tsh, q.1⟩

/-- Of "the seats are carried": a tree of the book has the listed shape. -/
theorem shape_of_seats {L : Laid} {B : TreeBook} (h : seatsCarriedB L B = true) (z : ℕ)
    (hz : z < B.trees.size) : (B.trees[z]?).map (·.shape) = L.shapes[z]? := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.trees.toList.map (·.shape) = L.shapes.take B.trees.size := eq_of_beq h.1.2
  rw [← List.getElem?_take_of_lt hz, ← e, List.getElem?_map, Array.getElem?_toList]

/-- **A part of a tree, as the guard reads it, is the written seat.** st₀: a statement whose
messages have the shapes of st's. -/
theorem writtenSeat_of_part {M : List OracleShape} {L : Laid} {st st₀ : Statement} {B : TreeBook}
    {roots : ℕ} (hM : msgShapesB M st₀ = true) (hL : seatsCarriedB L B = true)
    (hB : bookInOrderB 0 B roots = true)
    (hst : ∀ (o : ℕ) (x : OnBytes.Oracle), st.oracles[o]? = some x →
      ∃ x₀, st₀.oracles[o]? = some x₀ ∧ x₀.shape = x.shape)
    {o num t p : ℕ} {sh : OracleShape} {tsh : TreeShape} (h : Part1P st B o sh num tsh t p) :
    writtenSeat M L o = some ⟨o, sh, t, p, tsh, num⟩ := by
  obtain ⟨x, hx, ex⟩ := h.oracle
  obtain ⟨x₀, hx₀, ex₀⟩ := hst o x hx
  obtain ⟨T, hT, e1, e2⟩ := h.tree
  have ho : o < st₀.oracles.size := (Array.getElem?_eq_some_iff.1 hx₀).1
  have hp : o < B.place.size := (Array.getElem?_eq_some_iff.1 h.place).1
  have ht : t < B.trees.size := (Array.getElem?_eq_some_iff.1 hT).1
  have a1 : M[o]? = some sh := by
    rw [← msgShape_at hM o ho, hx₀, Option.map_some, ex₀, ex]
  have a2 : L.places[o]? = some (t, p) := by
    rw [← place_of_seats hL o hp]
    exact h.place
  have a3 : L.shapes[t]? = some tsh := by
    rw [← shape_of_seats hL t ht, hT, Option.map_some, e1]
  have a4 : num = t := by
    rw [← e2]
    exact numbers_of_book0 hB t T hT
  unfold writtenSeat
  rw [a1, Option.bind_some, a2, Option.bind_some, a3, Option.map_some, a4]

/-- **The test on the lists** (its clauses: the head of this file). -/
def closingSeatsTest (M : List OracleShape) (L : Laid) (q : P12) (p : K2.SwitchPlace) : Bool :=
  decide (q.nums.firstTree = 0) &&
  decide ((H2K.First.opensOf q (stA q).k).map (·.1.tree - q.nums.firstTree) = [76]) &&
  ((List.range L.places.length).all fun o =>
    (L.places.getD o (0, 0)).1 != 76 || o == 185 || o == 186) &&
  match writtenSeat M L 185, writtenSeat M L 186, layTrees (parL p).codes (parL p).sent with
  | some s, some f, some Ly =>
    decide (0 < s.sh.mainRows) && decide (f.sh.mainRows = 0) &&
    decide (s.t = 76) && decide (f.t = 76) && closingPlaceTest q p Ly &&
    seatIsTest (stA q) (parL p) Ly 0 s && seatIsTest (stA q) (parL p) Ly 1 f &&
    decide (f.sh.maskRows = 2 ^ (stA q).h) && decide (s.sh.mainDeg = 3) &&
    decide (s.sh.maskRows = 0) && decide (s.sh.mainRows = 2 ^ kk (stA q)) &&
    decide (s.tsh.logN =
      (((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.getD 0
        default).logN) &&
    decide (s.tsh.mainWidth + s.tsh.maskWidth =
      (Ly.shapes.getD 0 {}).mainWidth + (Ly.shapes.getD 0 {}).maskWidth)
  | _, _, _ => false

set_option maxRecDepth 1000000 in
/-- **The closed line**: at the written lists, the written place of the first chain's proximity test
and the written finish of the code switch the test says yes. -/
theorem closingSeats_written :
    finishW.any (closingSeatsTest OnBytes.Road.K4.mW LFull piLFull) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls, each with one thing changed: message 185 is listed in tree 75 · message 0 is listed in
tree 76 too · the test's first tree bears the number 1. The test says no. Alone a "false" could come
of a lacking finish; `closingSeats_written` shows that one is there. -/
theorem closingSeats_written_no :
    (finishW.any (closingSeatsTest OnBytes.Road.K4.mW
        { LFull with places := LFull.places.set 185 (75, 0) } piLFull) ||
      finishW.any (closingSeatsTest OnBytes.Road.K4.mW
        { LFull with places := LFull.places.set 0 (76, 2) } piLFull) ||
      finishW.any (closingSeatsTest OnBytes.Road.K4.mW LFull
        { piLFull with nums := { piLFull.nums with firstTree := 1 } })) = false := by
  decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.writtenSeat
#print axioms ProofFile.Honest.K12.AtProof.shape_of_seats
#print axioms ProofFile.Honest.K12.AtProof.writtenSeat_of_part
#print axioms ProofFile.Honest.K12.AtProof.closingSeatsTest
#print axioms ProofFile.Honest.K12.AtProof.closingSeats_written
#print axioms ProofFile.Honest.K12.AtProof.closingSeats_written_no
