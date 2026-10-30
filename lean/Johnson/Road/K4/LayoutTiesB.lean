-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LayoutTiesB.lean: THE TIE OF LETTERS `Meaning.ShapesTied`
(Johnson/Goal/Meaning/LaidInsideSeats.lean) AS A TEST WITH CODE. One definition, and two toys at
which it is evaluated. It imports the plain structures' files alone, so that a sheet can run it.

  `shapesTiedB codes shape layout num arr L grp`: for every array A of every link l of the layout
    whose message A.message is there in the request's shape: for each k below 25, each entry e of
    the plain lists L and each i below the number of e's shapes: the seat number i of e (beyond the
    seats' list: (0, 0)) is not in grp k, or its number by arr is not num l A.message, or the shape
    number i of e has that message's `padKey`. It walks lists alone: arrays × 25 × members.
  `toy_yes`, `toy_no`: **a control**: one link, one message, one array, one member at the seat
    (0, 0): where the member's shape is the message's the test says true; with one main row more it
    says false.

OBJECT: no block's text: public letters. USER: Johnson/Road/K4/LayoutTies.lean
(`shapesTied_of_B`). LETTERS: all seven, free.

Limits. It has run at the two toys alone: at no plan.
(Where this and lean/THEOREM.md differ, the page holds.) Where the layout names a
message that the
shape lacks, the array is passed over, as `Meaning.ShapesTied` passes it over. Nothing on
soundness. K04_law IS NOT PROVED BY THIS.
-/
import Johnson.Goal.Meaning.LaidInside
import Johnson.Desc.PlanMem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Road.K4.LayoutTies
open OnBytes.Params (ReqArray ReqLayout ReqShape ReqLink ReqMessage)
open VerifiableInference.Desc (MemberLists padKey)

/-- **The tie of letters, with code.** -/
def shapesTiedB (codes : OnBytes.Codes) (shape : ReqShape) (layout : ReqLayout)
    (num arr : Nat → Nat → Nat) (L : MemberLists) (grp : Nat → List (Nat × Nat)) : Bool :=
  layout.link.zipIdx.all fun x => x.1.all fun A =>
    match Meaning.messageAt shape x.2 A.message with
    | none => true
    | some m =>
      (List.range 25).all fun k => L.all fun e => (List.range e.1.length).all fun i =>
        !((grp k).contains (e.2.getD i (0, 0))) ||
          arr (e.2.getD i (0, 0)).1 (e.2.getD i (0, 0)).2 != num x.2 A.message ||
          padKey codes (e.1.getD i default).1 == padKey codes m.shape

/-! ## Two toys -/

/-- A shape with so many main rows. -/
def toyOracle (rows : Nat) : OnBytes.OracleShape := { mainRows := rows }

/-- A message of one main row. -/
def toyMessage : ReqMessage := { shape := toyOracle 1, leafClass := 0, moment := 0, life := 0 }

/-- One link with that one message. -/
def toyShape : ReqShape :=
  { (default : ReqShape) with link := [{ plain := 0, messages := [toyMessage] }] }

/-- One array in that message. -/
def toyLayout : ReqLayout :=
  { link := [[{ name := "a", message := 0, sizeI := 1, sizeC := 1, blocks := [] }]] }

/-- The test at the toy, the one member's shape having so many main rows. -/
def toyAt (rows : Nat) : Bool :=
  shapesTiedB {} toyShape toyLayout (fun _ _ => 0) (fun _ _ => 0)
    [([(toyOracle rows, 0)], [(0, 0)])] fun _ => [(0, 0)]

theorem toy_yes : toyAt 1 = true := by decide +kernel

/-- **A control**: the test can say no. -/
theorem toy_no : toyAt 2 = false := by decide +kernel

end Johnson.Road.K4.LayoutTies

#print axioms Johnson.Road.K4.LayoutTies.toy_yes
#print axioms Johnson.Road.K4.LayoutTies.toy_no
