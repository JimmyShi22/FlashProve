-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Fill/FillP1Plus.lean: four public tests on the verifier's state, with their rows, as
a part of their own that can be laid over a filling of the table of joints
(Johnson/Desc/First/Borders.lean). Definitions with code, and small theorems. No Mathlib beneath.

Why. The four names "K8.lay7", "K8.onThird", "K8.funsThird" and "pile.room" have left the layer
`fillP1` (FillP1.lean): their facts are taken at the states that the verifier reaches. Whoever types
a law at the wider filling, or states over which borders such a fact holds, still needs the names,
the tests and the rows at a path of their own.

Main names:
  `PlusData`: the planner's numbers that the tests read: a segment's planned data of the approximate
    range proof (our files: the smallness test); the segments' flags "leaves a row on the committed
    table"; how many entries the index masks' fresh ledger has.
  `lay7Name`, `onThirdName`, `funsThirdName`, `roomName`: the names, by segment. `plusItem`: which
    items are the four.
  `pubPlus d f`: the four tests over whatever says the other items: `lay7B`, `onThirdB`
    (Johnson/Desc/First/K8/Cond.lean), `funsThirdB` (K8/CondFuns.lean), `roomIsB`
    (Johnson/Top/H0/Walk/FrameEntriesDefs.lean).
  `rowK8`, `rowRoom`, `moreP1`: who makes, asks and drops the names.
  `fillP1Plus d Mg`: THE PART: pub := `pubPlus d Mg.pub`; more := `Mg.more.merge moreP1`; nothing
    else turns.
  `pubPlus_lay7` ... `pubPlus_else`, `fillP1Plus_pub`, `fillP1Plus_more`.

Limits. WHO MAKES WHAT IS WRITTEN BY READING: no law says here that a sub-protocol makes, keeps or
may drop a name. No test has run on a verifier's state by its authors' hand. Nothing on soundness.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.First.K8.Cond
import Johnson.Desc.First.K8.CondFuns
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.FillP1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place KindName)

/-- The planner's numbers that the four tests read. -/
structure PlusData where
  /-- a segment's planned data of the approximate range proof -/
  tl : Nat → Option HTailF2
  /-- the segments' flags, in order: does the segment leave a row on the committed table? -/
  fvs : List Bool
  /-- how many entries the index masks' fresh ledger has -/
  free0 : Nat

/-- The four names, by segment. -/
def lay7Name (m : Nat) : MoreName := (some m, "K8.lay7")
def onThirdName (m : Nat) : MoreName := (some m, "K8.onThird")
def funsThirdName (m : Nat) : MoreName := (some m, "K8.funsThird")
def roomName (m : Nat) : MoreName := (some m, "pile.room")

/-- A segment of this sort leaves a row on the weights. -/
def bears (sub : ModelPart) : Bool := sub != .attention

/-- The first segment from number m on that leaves a row on the weights. -/
def nextBearing (links : List ModelPart) (m : Nat) : Option Nat :=
  ((List.range links.length).drop m).find? fun i => (links[i]?).any bears

/-- Is the item one of the four? -/
def plusItem : Pub → Bool
  | .more (some _) name =>
    name == "K8.lay7" || name == "K8.onThird" || name == "K8.funsThird" || name == "pile.room"
  | _ => false

/-- **The four tests**, over whatever says the other items. -/
def pubPlus {P : Type} (d : PlusData) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .more (some m) name =>
      if name == "K8.lay7" then (d.tl m).any fun tlP => K8.Ready.lay7B tlP a.2
      else if name == "K8.onThird" then K8.Ready.onThirdB a.2
      else if name == "K8.funsThird" then K8.Ready.funsThirdB a.2
      else if name == "pile.room" then Johnson.Desc.First.Walk.Tied.roomIsB d.free0 d.fvs m a.2
      else f (.more (some m) name) a
    | q => f q a

/-- **Who makes, asks and drops the smallness test's names**, o the head's shift: "K8.lay7" and
"K8.onThird" are asked and dropped by the block of the reads' equations (piece 5 + o). "K8.lay7" is
made by the block at piece 1 + o, whose second half opens the segment and lays its planned data: at
every sort of segment; the blocks between keep it. "K8.onThird" is made by the block right in front
of the asker (piece 4 + o), whose quiet step closes the list of tables. At a layers' segment that
step lays the caller's own list: so there a third name, "K8.funsThird" (the tables as the claims
take them are there, and every one lies on the third vector of reads), is made by the caller's block
(piece 3 + o) and asked and dropped by the block at piece 4 + o. BY READING: no law says here that
these blocks make them. -/
def rowK8 (sub : ModelPart) (m piece : Nat) : MoreRow :=
  let o := shift sub
  if piece == 5 + o then
    { asks := [lay7Name m, onThirdName m], drops := [lay7Name m, onThirdName m] }
  else if piece == 4 + o then
    { makes := [onThirdName m]
      asks := if sub == .layers then [funsThirdName m] else []
      drops := if sub == .layers then [funsThirdName m] else [] }
  else if piece == 3 + o && sub == .layers then { makes := [funsThirdName m] }
  else if piece == 1 + o then { makes := [lay7Name m] }
  else {}

/-- **Who makes, asks and drops "pile.room"**: a name for each segment that leaves a row on the
weights: made for the first of these at segment 0's piece 1; asked, and kept, by the block that
opens "wo" (a layers' segment's piece 3; the head's piece 9); asked and dropped by the frame's block
"cleared" of that segment (piece 13 + 2 o), which takes the one entry and makes the next such
segment's. BY READING: no law says here that these blocks make them. -/
def rowRoom (links : List ModelPart) (sub : ModelPart) (m piece : Nat) : MoreRow :=
  let o := shift sub
  if piece == 1 && m == 0 then { makes := (nextBearing links 0).toList.map roomName }
  else if bears sub && piece == (if sub == .head then 9 else 3) then { asks := [roomName m] }
  else if bears sub && piece == 13 + 2 * o then
    { asks := [roomName m], drops := [roomName m]
      makes := (nextBearing links (m + 1)).toList.map roomName }
  else {}

/-- The layer's rows at the door: the two, list by list. -/
def moreP1 : More where
  rows := fun links p =>
    match p.link with
    | none => {}
    | some m =>
      match links[m]? with
      | none => {}
      | some sub =>
        { makes := (rowK8 sub m p.piece).makes ++ (rowRoom links sub m p.piece).makes
          asks := (rowK8 sub m p.piece).asks ++ (rowRoom links sub m p.piece).asks
          drops := (rowK8 sub m p.piece).drops ++ (rowRoom links sub m p.piece).drops }

/-- **THE PART**: the four tests and their rows, laid over a filling; nothing else of it turns. -/
def fillP1Plus {P W : Type} (d : PlusData) (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    pub := pubPlus d Mg.pub
    more := Mg.more.merge moreP1 }

section
variable {P W : Type} (d : PlusData) (f : Pub → P × S → Bool) (Mg : Meaning P W)

theorem pubPlus_lay7 (m : Nat) (a : P × S) :
    pubPlus d f (moreItem (lay7Name m)) a = (d.tl m).any fun tlP => K8.Ready.lay7B tlP a.2 := rfl

theorem pubPlus_onThird (m : Nat) (a : P × S) :
    pubPlus d f (moreItem (onThirdName m)) a = K8.Ready.onThirdB a.2 := rfl

theorem pubPlus_funsThird (m : Nat) (a : P × S) :
    pubPlus d f (moreItem (funsThirdName m)) a = K8.Ready.funsThirdB a.2 := rfl

theorem pubPlus_room (m : Nat) (a : P × S) :
    pubPlus d f (moreItem (roomName m)) a =
      Johnson.Desc.First.Walk.Tied.roomIsB d.free0 d.fvs m a.2 := rfl

/-- Every other item is handed on. -/
theorem pubPlus_else (q : Pub) (h : plusItem q = false) (a : P × S) : pubPlus d f q a = f q a := by
  cases q with
  | more seg name =>
    cases seg with
    | none => rfl
    | some m =>
      simp only [plusItem, Bool.or_eq_false_iff] at h
      show (if name == "K8.lay7" then _ else if name == "K8.onThird" then _
        else if name == "K8.funsThird" then _ else if name == "pile.room" then _ else _) = _
      rw [if_neg (by rw [h.1.1.1]; simp), if_neg (by rw [h.1.1.2]; simp),
        if_neg (by rw [h.1.2]; simp), if_neg (by rw [h.2]; simp)]
  | _ => rfl

theorem fillP1Plus_pub : (fillP1Plus d Mg).pub = pubPlus d Mg.pub := rfl
theorem fillP1Plus_more : (fillP1Plus d Mg).more = Mg.more.merge moreP1 := rfl

end

end VerifiableInference.Desc.First.FillP1
