-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SixAside.lean: PairAside.lean's DEVICE, WIDENED: OF A BORDER INSIDE A LAYERS'
LINK NOT TWO BUT SIX PARTS ARE SET ASIDE, AND LAID BACK: `less6`, `withSix`, `sixOf`, **`eta_six`**.
Ten definitions, four theorems. General; no premise on the shape; nothing is evaluated.

Purpose. Inside a layers' link the shape at a border is long by what the link's own rounds have
left: in a timed run at link 0, 97 of 100 nodes of such a border lay in six parts (not shown
here): look and lookHeard (PairAside.lean's pair); in the own record: what was heard of the lookup
(its calls and its rows: two fields), and the batched sumcheck's two end forms and its row. A
written border holds the shape LESS these; the piece behind starts from that with the parts that the
piece in front left, as a closed term. The own record's fields are no options: they are EMPTIED, not
laid to none: so the way back is of another make than the pair's.

Main names.
* `OwnPart`, `Six`: the own record's five fields; the pair with these, where an own record is there.
* `ownPart o`, `withOwn o q`, `noOwn`: the five fields of o; o with five fields laid; the five,
  empty.
* `sixOf x`, `withSixC a p`, `withSix x p`, `less6 x`, `sixE r`: the parts of a shape; laying them;
  the shape less them (the pair to none, the five emptied); the parts that a run leaves, nothing
  where it refuses.
* `withOwn_self`; **`eta_six`**: less6 x = c → x = withSix c (sixOf x); `ok_of_less6`:
  PairAside.lean's ok_of_less, at the six; `less6_setters`: less6 by the library's own setters
  layLook, layLookHeard, layOwn.

Limits. SEVEN FIELDS IN SIX PARTS: the calls and the rows count as one part. withSixC lays five
fields only where the shape HAS an own record; where it has one and none are handed in, it lays the
empty five. sixE answers ((none, none), none) at a refused run: a fact on a later piece alone can be
true although the piece in front refused. No join is stated here: JoinPieces.lean's tests and laws
speak of the pair alone; JoinMany.lean has the join for the six. That a member does not read the six
is said nowhere. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.PairAside

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.SixAside
open OnBytes OnBytes.Model
open Johnson.AtFull.Shape
open Johnson.AtFull.Shape.PairAside (Pair pairOf withLkC)
open VerifiableInference.Desc.First.Shape

/-- What is set aside of the layers' own rounds' record: the lookup's calls and rows as heard; the
batched sumcheck's two end forms and its row. -/
abbrev OwnPart : Type := Array Call × List AffSh × AffSh × AffSh × AffSh

/-- The parts that are set aside: the pair (look, lookHeard), and the own record's five fields where
such a record is there. -/
abbrev Six : Type := Pair × Option OwnPart

/-- The own record's five fields. -/
def ownPart (o : OwnSh) : OwnPart := (o.H.fo.shape.calls, o.H.fo.rows, o.K.Alin, o.K.Blin, o.K.rowS)

/-- The own record with these five fields laid. -/
def withOwn (o : OwnSh) (q : OwnPart) : OwnSh :=
  { o with
    H := { o.H with
      fo := { o.H.fo with shape := { o.H.fo.shape with calls := q.1 }, rows := q.2.1 } }
    K := { o.K with Alin := q.2.2.1, Blin := q.2.2.2.1, rowS := q.2.2.2.2 } }

/-- The five fields, empty. -/
def noOwn : OwnPart := (#[], [], AffSh.mk [] [], AffSh.mk [] [], AffSh.mk [] [])

/-- The parts of a shape. -/
def sixOf (x : ShA) : Six := (pairOf x, x.1.own.map ownPart)

/-- The chain's shape with the parts laid: the pair; and, where an own record stands, the five
fields that are handed in. Two silent answers: where an own record stands and none are handed in,
its five are emptied; where none stands, five that are handed in are dropped. -/
def withSixC (a : ChainSh) (p : Six) : ChainSh :=
  (withLkC a p.1).layOwn (a.own.map fun o => withOwn o (p.2.getD noOwn))

/-- The shape with the parts laid. -/
def withSix (x : ShA) (p : Six) : ShA := (withSixC x.1 p, x.2)

/-- The shape less the parts: the pair laid to none, the five fields emptied. -/
def less6 (x : ShA) : ShA := withSix x ((none, none), none)

/-- The parts that a run leaves; nothing where it refuses. -/
def sixE (r : Except String ShA) : Six :=
  match r with
  | .ok x => sixOf x
  | .error _ => ((none, none), none)

/-- Whatever was laid, laying the record's own five fields gives the record back. -/
theorem withOwn_self (o : OwnSh) (q : OwnPart) : withOwn (withOwn o q) (ownPart o) = o := rfl

/-- **A shape is what it is less the parts, with its own parts laid back.** The premise only names
less6 x: it can hold at no c but one with nothing at the pair and the five emptied. -/
theorem eta_six {x c : ShA} (h : less6 x = c) : x = withSix c (sixOf x) := by
  subst h
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
    F⟩ := x
  cases a15 with
  | none => rfl
  | some o => rfl

/-- Where a run returns x and x less the parts is c, the run returned c with its own parts. -/
theorem ok_of_less6 {r : Except String ShA} {x c : ShA} (hr : r = .ok x) (h : less6 x = c) :
    r = .ok (withSix c (sixE r)) := by
  subst hr
  exact congrArg Except.ok (eta_six h)

/-- less6 by the library's own setters. -/
theorem less6_setters (x : ShA) :
    less6 x = ((((x.1.layLook none).layLookHeard none).layOwn
      (x.1.own.map fun o => withOwn o noOwn)), x.2) := by
  obtain ⟨⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩,
    F⟩ := x
  rfl

end Johnson.AtFull.Shape.SixAside

#print axioms Johnson.AtFull.Shape.SixAside.OwnPart
#print axioms Johnson.AtFull.Shape.SixAside.Six
#print axioms Johnson.AtFull.Shape.SixAside.ownPart
#print axioms Johnson.AtFull.Shape.SixAside.withOwn
#print axioms Johnson.AtFull.Shape.SixAside.noOwn
#print axioms Johnson.AtFull.Shape.SixAside.sixOf
#print axioms Johnson.AtFull.Shape.SixAside.withSixC
#print axioms Johnson.AtFull.Shape.SixAside.withSix
#print axioms Johnson.AtFull.Shape.SixAside.less6
#print axioms Johnson.AtFull.Shape.SixAside.sixE
#print axioms Johnson.AtFull.Shape.SixAside.withOwn_self
#print axioms Johnson.AtFull.Shape.SixAside.eta_six
#print axioms Johnson.AtFull.Shape.SixAside.ok_of_less6
#print axioms Johnson.AtFull.Shape.SixAside.less6_setters
