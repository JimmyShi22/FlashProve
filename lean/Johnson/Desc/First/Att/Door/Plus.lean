-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Plus.lean: kind K5: A SMALL WIDER FILLING OF THE TABLE OF JOINTS'
PARAMETERS, AT WHICH THE KIND's TIE IS TYPED. Definitions with code, and small lemmas. No Mathlib.

Why. The composed filling strikes thirteen names of public tests from the table, and its "in order"
leaves out conjuncts of the same sort: each says a fact that holds at every state that the verifier
reaches. The kind's law spends four such facts in front of its sub-protocol (three are struck
names; the fourth, a conjunct that "in order" leaves out), AND A FIFTH SORT THAT IS NO STRUCK NAME:
the kept rows of what the verifier has received from the lookup argument name no
entry: the book carries the plan's seats · the statement's messages have the plan's shapes · the
open link's copy of the live request has the plan's shape and layout · the statement's codes are the
plan's. A tie that is typed at a wider filling serves at the narrower one in the table's second form
(tiedAtR_of_widen, Johnson/Desc/Sound/PlusDoor.lean), where the facts come
from the condition "this state is reached".

Main names:
  `moreOver9 M0`: the parts' lists of extra public tests merged over M0, in the composed filling's
    order, before the strike.
  `isThree`, `leavesBut3`: the three names that stay here: K12.seatsCarried · K12.msgShapes ·
    frame.liveIs (at a segment); every other name that leaves is struck.
  `bareAttB`, `leftAttB`, `bareMoreAtt`, `isOurs`, `isWide`: a fourth and a fifth name, of K5's
    files, AT THE WIDER FILLING ALONE: K5.rowsBare · K5.lookLeft (at an attention segment): made at
    piece 2 (the lookup argument), asked and dropped at piece 3 (the kind's own): after the form of
    K4.rowsBare | K4.lookLeft at the layers' segments
    (Johnson/Desc/First/FillBare.lean: its two tests answer false at every attention state: so the
    like is written here at the other constructor; the heart of the second, leftAtB, general in what
    was received and the ledger, IS CALLED). K5.lookLeft: all else that the kind's
    runs want of the TEXT of the forms and of the unfinished sumcheck that the lookup argument has
    left.
  `isThreeQ`, `isWideQ`: the item is one of the three names | of the five. `pubPPlus b`:
    what an item says beside its test at the wider filling: at the five names nothing
    (True), elsewhere b: so no table of the base b need know K5's files' names.
  `morePlus M0`: the wider list: moreOver9 M0 with the two owners' three parts and bareMoreAtt (both
    names) laid beside, struck by leavesBut3.
  `pubPlus L M d3 b`: the wider tests: at the three names THE OWNERS' OWN TESTS (atFirstSeats ·
    atFirstShapes · liveIsC); at the fourth bareAttB; at the fifth leftAttB; elsewhere b.
  `ioPlus cs io`: the wider "in order": io, and the statement's codes are cs.
  `pubPlus_else`: at an item that is no name pubPlus is b. `pubPlus_more_else`: the like at a name
    that is not wide. `pubPlus_seats`, `pubPlus_shapes`, `pubPlus_live`, `pubPlus_bare`,
    `pubPlus_left`: the five arms.
THE WIDENING HOLDS ONLY WHAT THE KIND SPENDS; that no smaller one serves is not shown. It pays no
fact. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.SmallDoor
import Johnson.Desc.First.Att.Door.Door
import Johnson.Desc.First.Look.K3LiveIs
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.First.FillSent
import Johnson.Desc.First.FillSentLater
import Johnson.Desc.First.FillBare
import Johnson.Desc.K12.Door.Door
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.K13.Law.SitsDoor
import Johnson.Desc.First.Close.Law.FillRowFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (K3Data liveIsC liveMore)
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstShapes k12More shapesMore)

/-- The parts' lists merged over M0, in the composed filling's order, before the strike. -/
def moreOver9 (M0 : More) : More :=
  ((((((M0.merge rowMore).merge FillBare.leftMore).merge FillSent.sent1More).merge FillSent.sentMore).merge
    H2K5.Door.more).merge K13.Law.wSitsMore)

/-- The three names that the kind's law spends. -/
def isThree : MoreName → Bool
  | (none, s) => s == "K12.seatsCarried" || s == "K12.msgShapes"
  | (some _, s) => s == "frame.liveIs"

/-- "K5.rowsBare": an attention segment is open, something is held as received from the lookup
argument, and its kept rows name no entry. -/
def bareAttB (s : S) : Bool :=
  match s.here with
  | .att a => a.lookHeard.any fun g => g.rows.toList.all fun f => f.ents.isEmpty
  | _ => false

/-- "K5.lookLeft": an attention segment is open, something is held as received from the lookup
argument, and the test leftAtB (FillBare.lean) says yes at it and the segment's ledger. THAT TEST
HAS RUN AT NO HONEST STATE (its own file's limits: "nothing says here who makes it" · "the test has
not run"). -/
def leftAttB (s : S) : Bool :=
  match s.here with
  | .att a => a.lookHeard.any fun g => FillBare.leftAtB g a.F
  | _ => false

/-- The two names' rows. -/
def bareMoreAtt : More where
  rows links p :=
    match p.link with
    | some m =>
      if links[m]? == some .attention then
        if p.piece == 2 then { makes := [(some m, "K5.rowsBare"), (some m, "K5.lookLeft")] }
        else if p.piece == 3 then
          { asks := [(some m, "K5.rowsBare"), (some m, "K5.lookLeft")], drops := [(some m, "K5.rowsBare"), (some m, "K5.lookLeft")] }
        else {}
      else {}
    | none => {}

/-- The fourth and the fifth name. -/
def isOurs : MoreName → Bool
  | (some _, s) => s == "K5.rowsBare" || s == "K5.lookLeft"
  | _ => false

/-- One of the five. -/
def isWide (n : MoreName) : Bool := isThree n || isOurs n

/-- The item is one of the three names. -/
def isThreeQ : Pub → Bool
  | .more n s => isThree (n, s)
  | _ => false

/-- The item is one of the five names. -/
def isWideQ : Pub → Bool
  | .more n s => isWide (n, s)
  | _ => false

/-- **What an item says beside its test, at the wider filling**: at the five names nothing;
elsewhere what b says. -/
def pubPPlus {P : Type} (b : Pub → P × S → Prop) : Pub → P × S → Prop :=
  fun q a => if isWideQ q = true then True else b q a

/-- Every name that leaves, but the three. -/
def leavesBut3 (n : MoreName) : Bool := leavesName n && !isThree n

/-- **The wider list of extra public tests.** -/
def morePlus (M0 : More) : More :=
  ((((moreOver9 M0).merge (k12More.merge shapesMore)).merge liveMore).merge bareMoreAtt).strike leavesBut3

section
variable {P : Type}

/-- **The wider tests**: the owners' own at the three names. -/
def pubPlus (L : Laid) (M : List OracleShape) (d3 : K3Data) (b : Pub → P × S → Bool) (q : Pub)
    (a : P × S) : Bool :=
  match q with
  | .more n s =>
    if isThree (n, s) then
      (if s == "K12.seatsCarried" then atFirstSeats L a.2
       else if s == "K12.msgShapes" then atFirstShapes M a.2 else liveIsC d3 a.2)
    else if isOurs (n, s) then (if s == "K5.rowsBare" then bareAttB a.2 else leftAttB a.2)
    else b q a
  | _ => b q a

/-- **The wider "in order".** -/
def ioPlus (cs : Codes) (io : P × S → Bool) (a : P × S) : Bool := io a && decide (a.2.st.codes = cs)

variable (L : Laid) (M : List OracleShape) (d3 : K3Data) (b : Pub → P × S → Bool)

theorem pubPlus_more_else {n : Option Nat} {s : String} (h : isWide (n, s) = false) (a : P × S) :
    pubPlus L M d3 b (.more n s) a = b (.more n s) a := by
  obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.1 h
  show (if isThree (n, s) then _ else if isOurs (n, s) then _ else _) = _
  rw [h1, h2]
  rfl

theorem pubPlus_else {q : Pub} (h : ∀ n s, q ≠ .more n s) (a : P × S) : pubPlus L M d3 b q a = b q a := by
  cases q <;> first | rfl | exact absurd rfl (h _ _)

theorem pubPlus_seats (a : P × S) :
    pubPlus L M d3 b (.more none "K12.seatsCarried") a = atFirstSeats L a.2 := rfl

theorem pubPlus_shapes (a : P × S) :
    pubPlus L M d3 b (.more none "K12.msgShapes") a = atFirstShapes M a.2 := rfl

theorem pubPlus_live (m : Nat) (a : P × S) :
    pubPlus L M d3 b (.more (some m) "frame.liveIs") a = liveIsC d3 a.2 := rfl

theorem pubPlus_bare (m : Nat) (a : P × S) :
    pubPlus L M d3 b (.more (some m) "K5.rowsBare") a = bareAttB a.2 := rfl

theorem pubPlus_left (m : Nat) (a : P × S) :
    pubPlus L M d3 b (.more (some m) "K5.lookLeft") a = leftAttB a.2 := rfl

end

end H2K5.Door

#print axioms H2K5.Door.pubPlus_more_else
#print axioms H2K5.Door.pubPlus_else
#print axioms H2K5.Door.pubPlus_seats
#print axioms H2K5.Door.pubPlus_shapes
#print axioms H2K5.Door.pubPlus_live
#print axioms H2K5.Door.pubPlus_bare
#print axioms H2K5.Door.pubPlus_left
