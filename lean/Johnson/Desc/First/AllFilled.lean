-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/AllFilled.lean: DOES ANY ITEM THAT THE PROMISE ASKS AT A BORDER FALL THROUGH ALL
LAYERS OF THE TABLE OF JOINTS' FILLING TO THE MEANING BENEATH? Tests with code. No Mathlib.
Why. The composed filling (`mgAll`, Johnson/Desc/Sound/MgAll.lean) hands a public item that no layer
answers, and the field worth outside the lookups' pieces and names, to the meaning beneath. At the
closed base (Johnson/Desc/Sound/MgBase.lean) that is "false": the promise then fails at every border
at
which such an item is asked. Whether there is such a border is a question on the table's lists.
  `askedAt M links ps`: border by border: the public items that the promise asks there: the open
    public set, and the items tied to the open items (as `pubHeld`,
    Johnson/Desc/First/Borders.lean).
  `unfilled D M links ps`: for a print: (border's number, item) wherever `whoFills` names no layer.
  `allFilled D M links ps`: there is none.
  `worthNamed X i`: an item worth m k r stands at one of the lookups' two pieces of segment m, under
  a
    name that the piece's arm answers (the digits': planes, keys; the calls': planes, keys, rider).
  `worthFilled X links ps`: so at every open item of every border.
  `allFilled_mem`: the first test's yes, border by border and item by item.
Limits: `whoFills` says that a layer's TEST claims the item; that the layer's answer is right is
that
layer's. `worthNamed` restates the arms' names: it is held against them by no theorem here. Nothing
on
soundness.

-/
import Johnson.Desc.First.PubAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Look (k3SortAt)

/-- Border by border: the public items that the promise asks there. -/
def askedAt (M : More) (links : List ModelPart) (ps : List Place) : List (List Pub) :=
  (pubSets M links ps).zipWith (fun Q O => Q ++ pubOfItems O) (openSets links ps (start links))

/-- For a print: where no layer claims an asked item. -/
def unfilled (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) : List (Nat × Pub) :=
  (askedAt M links ps).zipIdx.flatMap fun x =>
    (x.1.filter fun q => (whoFills D q).isNone).map fun q => (x.2, q)

/-- **No asked public item falls to the meaning beneath.** -/
def allFilled (D : PubData) (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (askedAt M links ps).all fun Q => Q.all fun q => (whoFills D q).isSome

/-- An item worth stands at a piece and under a name that an arm of the lookups' layer answers. -/
def worthNamed (X : OnBytes.Model.Verify.Public) : Item → Bool
  | .worth m k r =>
    match k3SortAt X m k with
    | some true => r == "planes" || r == "keys"
    | some false => r == "planes" || r == "keys" || r == "rider"
    | none => false
  | _ => true

/-- So at every open item of every border. -/
def worthFilled (X : OnBytes.Model.Verify.Public) (links : List ModelPart) (ps : List Place) : Bool :=
  (openSets links ps (start links)).all fun O => O.all (worthNamed X)

theorem allFilled_mem (D : PubData) (M : More) (links : List ModelPart) (ps : List Place)
    (h : allFilled D M links ps = true) (Q : List Pub) (hQ : Q ∈ askedAt M links ps) (q : Pub)
    (hq : q ∈ Q) : (whoFills D q).isSome = true :=
  List.all_eq_true.1 (List.all_eq_true.1 h Q hQ) q hq

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.allFilled_mem
