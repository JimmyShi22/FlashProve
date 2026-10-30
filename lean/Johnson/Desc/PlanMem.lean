-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/PlanMem.lean: THE SAMPLED MEMBERS OF A CHAIN's SENDINGS AS PLAIN LISTS, and tests on
them with code. It imports Johnson/Desc/SeatAt.lean alone. NOTHING IS PROVED IN THIS FILE.
  `MemberLists`: one entry a sending: its sampled oracle messages' shapes, each with its radius, and
    their seats (the tree's number through the file, the tenant), in the same order.
  `seatsFitB F codes L`: no member has a fault (`seatFaultAt`, SeatAt.lean), and each entry has as
    many seats as shapes. `allSeats L`: all seats, in order. `shapeAtSeat L x`: the shape of the
    member at a seat.
  `padKey codes s`: the five numbers that the test on a pad's place (`padB`, SeatAt.lean) and a
    message's ranges read. `padSame codes L arr`: MEMBERS WITH ONE NUMBER HAVE ONE `padKey`: a
    copy's pad stands where its original's stands, and their ranges are one. `oneAnswer L`: every
    member has just one answer (`padB` is the pad at one answer).
What a yes gives: Johnson/Desc/Sound/PlanMemProofs.lean.
Who makes such lists: whoever evaluates the plan (the rows of Johnson/G/LinkSig.lean for the
shapes and radii; `OnBytes.layTrees` for the seats). THAT THE LISTS ARE THE PLAN's IS SAID BY
NOTHING HERE.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- One entry a sending: the sampled messages' shapes with their radii, and their seats. -/
abbrev MemberLists : Type := List (List (OnBytes.OracleShape × Nat) × List (Nat × Nat))

/-- No member has a fault, and each entry has as many seats as shapes. -/
def seatsFitB {Xi : Type} (F : FileDescription Xi) (codes : OnBytes.Codes) (L : MemberLists) : Bool :=
  L.all fun x => x.1.length == x.2.length && (List.range x.1.length).all fun i =>
    (seatFaultAt F codes "" (x.1.getD i default).1 (x.2.getD i (0, 0)).1
      (x.2.getD i (0, 0)).2).isNone

/-- All seats, in order. -/
def allSeats (L : MemberLists) : List (Nat × Nat) := L.flatMap (·.2)

/-- The shape of the member at a seat. -/
def shapeAtSeat (L : MemberLists) (x : Nat × Nat) : Option OnBytes.OracleShape :=
  L.findSome? fun e => ((e.1.zip e.2).find? fun y => y.2 == x).map (·.1.1)

/-- The five numbers that the test on a pad's place and a message's ranges read. -/
def padKey (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Nat × Nat × Nat × Nat × Nat :=
  (s.maskRows, s.mainRows, s.mainDeg, (codes.base.getD s.code default).ell,
    (codes.mask.getD s.maskCode default).ell)

/-- **Members with one number have one `padKey`.** By index, as the members are made of the lists:
member i of an entry has the shape number i and the seat number i. -/
def padSame (codes : OnBytes.Codes) (L : MemberLists) (arr : Nat → Nat → Nat) : Bool :=
  L.all fun e => (List.range e.1.length).all fun i =>
    L.all fun e' => (List.range e'.1.length).all fun i' =>
      arr (e.2.getD i (0, 0)).1 (e.2.getD i (0, 0)).2 !=
          arr (e'.2.getD i' (0, 0)).1 (e'.2.getD i' (0, 0)).2 ||
        padKey codes (e.1.getD i default).1 == padKey codes (e'.1.getD i' default).1

/-- Every member has just one answer. -/
def oneAnswer (L : MemberLists) : Bool := L.all fun e => e.1.all fun s => s.1.answers == 1

end VerifiableInference.Desc
