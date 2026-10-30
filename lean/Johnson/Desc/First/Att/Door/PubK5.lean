-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/PubK5.lean: K5's FILES' LAYER OF THE FILLING OF THE TABLE OF JOINTS' MEANING: ITS HALF WITH CODE: pubK5 : ‹data› → (Pub → P × S → Bool) → (Pub → P × S → Bool). No Mathlib. BESIDE THE TABLE: it turns nothing of it.
K5's SIX ITEMS, EACH LAID AT ATTENTION SEGMENTS ALONE (an item that several sorts of segment share is laid by sort; the others are handed on):
  callerIn m: nothing is heard at the kind's seat; the lookup's return is held; the ledger's next free slot is the plan's (the calls' first slot + the lookup's scalars, off the public record) (callerIn3B, Johnson/Desc/First/Att/Door/DoorBools.lean).
  look m: lookAttB: BOTH HOMES OF WHAT THE LOOKUP ON THE CALLS RETURNED ARE LAID AND HOLD ONE THING (sameHeardB: field by field; of the leaves' sumcheck's list of variables the length alone) · its last claim's form cEnd names no entry · every slot that cEnd names is below the number of slots and filled.
  more (some m) "K5.readsThere": readsThereB (Johnson/Desc/First/Att/Door/ReadsThereB.lean).
  more (some m) "K5.okAt": okThereB at the geometry of the plan of the segment's group (Johnson/Desc/First/Att/Door/OkThereB.lean).
  more (some m) "K5.liveReq": liveReqB at bornOf shape m (Johnson/Desc/First/Att/K05DoorB.lean: no Mathlib; bornOf | keptOf | shapesOf: the library's Look.bornAt | keptAt | shapesCalls typed out off the request's shape alone: tied by rfl in ties/ (a folder that is not in this library)).
  more (some m) "K5.plain": plainThereB at the number of the array of the reads and the width of the plan of the segment's group (Johnson/Desc/First/Att/Door/PlainThereB.lean).
TWO LETTERS OF K5's LAWS THAT ARE NO ITEMS OF K5's: seatsLetterB (for «K12.seatsCarried») · shapesLetterB (for «K12.msgShapes»: that sentence has a name in other files: one item, one owner).
EVERY OTHER ITEM, AND THESE SIX AT ANOTHER SORT OF SEGMENT, IS HANDED ON TO THE FUNCTION THAT IS GIVEN. WHERE THE PUBLIC RECORD HAS NO PLAN, PLACE OR SHAPE AT AN ATTENTION LINK THE ITEM IS FALSE: OF callerIn · K5.readsThere · K5.okAt · K5.plain; look m READS NO LETTER; K5.liveReq READS THE LETTER shape ALONE: WHERE IT HAS NO LINK m: born #[].
look m AGAINST THE ITEM's OWN WORDS ("every slot that its last claim names is filled in the ledger; and both readers of what it returned give one thing"): lookAttB SAYS MORE: the last claim's form names no entry; each slot that it names lies below the ledger's number of slots · AND LESS: "one thing" is sameHeardB: field by field; of the leaves' sumcheck's variables the length alone (what its yes gives: sameHeard_gives, Johnson/Desc/First/Att/Door/LookGives.lean) · IDLE WHERE THE LAST CLAIM's FORM IS A CONSTANT: its two last clauses then pass for nothing.
  K5Data: links (the table's own list) · W (the public record) · ownOf (the seats that a form may read in front of the second sending: Numbers.sent m 0) · shape (the request's shape) · seatsOf (for seatsLetterB alone).
  k5Item d q: is the item one of this layer's?
-/
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Att.GeoOf
import Johnson.Desc.First.Att.Door.ReadsThereB
import Johnson.Desc.First.Att.Door.DoorBools
import Johnson.Desc.First.Att.Door.OkThereB
import Johnson.Desc.First.Att.Door.Door
import Johnson.Desc.First.Att.Door.PlainThereB
import Johnson.Desc.First.Att.K05DoorB
import OnBytes.Params.DeriveReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First

def sameEnt (a b : Ent) : Bool := a.tree == b.tree && a.row == b.row && a.idx == b.idx && a.coef == b.coef

def sameAff (a b : Aff) : Bool :=
  a.ents.size == b.ents.size && (a.ents.toList.zip b.ents.toList).all (fun x => sameEnt x.1 x.2) &&
    a.slots == b.slots && a.const == b.const

def sameAffs (a b : Array Aff) : Bool :=
  a.size == b.size && (a.toList.zip b.toList).all fun x => sameAff x.1 x.2

/-- Two records of what a lookup returned hold one thing: field by field; of the leaves' sumcheck's list of variables the length alone. -/
def sameHeardB (g h : Forest.Heard) : Bool :=
  VerifiableInference.Desc.K3.sameShapeAll g.shape h.shape && g.theta == h.theta && g.alpha == h.alpha && g.a == h.a &&
    sameAffs g.rows h.rows && sameAff g.leaves.start h.leaves.start && g.leaves.target == h.leaves.target &&
    g.leaves.eps == h.leaves.eps && g.leaves.claim == h.leaves.claim && g.leaves.first == h.leaves.first &&
    g.leaves.vars.size == h.leaves.vars.size && g.leaves.r == h.leaves.r && g.leaves.ended == h.leaves.ended &&
    g.leaves.rowMade == h.leaves.rowMade && g.leaves.started == h.leaves.started && g.leavesA == h.leavesA &&
    g.sBit == h.sBit && g.zx == h.zx && g.zy == h.zy && g.e == h.e && sameAff g.cEnd h.cEnd && g.zb0 == h.zb0 &&
    g.zb1 == h.zb1 && g.tT == h.tT && g.zk == h.zk && g.owedObjects == h.owedObjects &&
    g.owedPlanes == h.owedPlanes && g.owedJoin == h.owedJoin

/-- The item look m at an attention segment, with the bound on the slots as a letter (cap: of the open ledger): for a control. -/
def lookAttUpTo (cap : Fork → Nat) (s : S) : Bool :=
  match s.here with
  | .att a =>
    match a.g, a.lookHeard with
    | some g, some gL =>
      sameHeardB g gL && gL.cEnd.ents.isEmpty &&
        gL.cEnd.slots.toList.all fun x => Decidable.decide (x.1 < cap a.F) && a.F.gotF.getD x.1 false
    | _, _ => false
  | _ => false

/-- **The item look m at an attention segment.** -/
def lookAttB (s : S) : Bool := lookAttUpTo (·.ns) s

/-- The layer's data. -/
structure K5Data where
  links : List ModelPart
  W : Verify.Public
  ownOf : Nat → List (Nat × Nat)
  /-- the request's shape (the first chain's parameters') -/
  shape : Params.ReqShape
  /-- link by link: the seats (tree, tenant) of the messages that stand sent when the lookup's shift is drawn, in their order: THE PIN's ITEM's LETTER: for seatsLetterB alone -/
  seatsOf : Nat → List (Nat × Nat) := fun _ => []

/-- As what each kept message of link l was first sent. OFF THE SHAPE ALONE. (Look.bornAt, typed out.) -/
def bornOf (shape : Params.ReqShape) (l : Nat) : Array (Nat × Nat) :=
  (((reqGroups shape)[l]?).map (·.born)).getD #[]

/-- The kept messages that are sent anew in link l's first prover's message. (Look.keptAt, typed out.) -/
def keptOf (shape : Params.ReqShape) (l : Nat) : List KeptTarget :=
  (((reqGroups shape)[l]?).map Params.keptOf).getD []

/-- The shapes of the messages that stand sent when the lookup's shift is drawn: the kept ones, then the link's own of moment 0. (shapesCalls, typed out.) -/
def shapesOf (shape : Params.ReqShape) (l : Nat) : List OracleShape :=
  (keptOf shape l).map (·.shape) ++
    ((((shape.link[l]?).map (·.messages)).getD []).takeWhile fun m => Decidable.decide (m.moment ≤ 0)).map (·.shape)

def K5Data.isAtt (d : K5Data) (m : Nat) : Bool := d.links[m]? == some .attention

/-- The caller's first slot at link m, off the public record. -/
def K5Data.first? (d : K5Data) (m : Nat) : Option Nat :=
  (Look.placeAt d.W m false).bind fun pC => pC.shape.map fun hC => pC.first + Forest.elems hC

/-- Is the item one of this layer's? -/
def k5Item (d : K5Data) : Pub → Bool
  | .callerIn m => d.isAtt m
  | .look m => d.isAtt m
  | .more (some m) n =>
    d.isAtt m && (n == "K5.readsThere" || n == "K5.okAt" || n == "K5.liveReq" || n == "K5.plain")
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. -/
def pubK5 {P : Type} (d : K5Data) (f : Pub → P × S → Bool) : Pub → P × S → Bool :=
  fun q a =>
    match q with
    | .callerIn m => if d.isAtt m then (d.first? m).any fun n => callerIn3B n a.2 else f q a
    | .look m => if d.isAtt m then lookAttB a.2 else f q a
    | .more (some m) n =>
      if d.isAtt m && n == "K5.readsThere" then readsThereB d.W (d.ownOf m) a.2
      else if d.isAtt m && n == "K5.okAt" then (d.W.A[m / 2]?).any fun p => okThereB (Att.P.geoOf p.S) a.2
      else if d.isAtt m && n == "K5.liveReq" then Att.P.liveReqB (bornOf d.shape m) a.2
      else if d.isAtt m && n == "K5.plain" then (d.W.A[m / 2]?).any fun p => plainThereB p.iU3 p.nW a.2
      else f q a
    | q => f q a

/-- NO ITEM OF K5's: K5's LAW's LETTER for «K12.seatsCarried» (with membersHeld): the book places the live request's message number k at seatsOf m's entry k, and that seat lies in ownOf m. For the walk to print beside, wherever «K5.liveReq» is open. AT A LIST CUT SHORT IT SAYS YES FOR NOTHING: it tests each entry that the letter has, not that the letter is whole: print the list's length against shapesOf's. -/
def seatsLetterB (d : K5Data) (m : Nat) (s : S) : Bool :=
  Att.P.seatsAtB (keptOf d.shape m).length (d.seatsOf m) (d.ownOf m) s

/-- NO ITEM OF K5's EITHER: K5's LAW's LETTER for «K12.msgShapes»: the statement's oracle of each message that stands sent when the lookup's shift is drawn has the plan's shape. For the walk to print beside. dk: 0; 1 for a control (one kept message more). THE SAME IDLE YES AT A LIST CUT SHORT; AND WHERE THE LETTER shape HAS NO LINK m IT SAYS YES AT EVERY RECORD WITH AN OPEN LINK (shapes_idle). -/
def shapesLetterB (d : K5Data) (m : Nat) (s : S) (dk : Nat := 0) : Bool :=
  Att.P.shapesAtB ((keptOf d.shape m).length + dk) (shapesOf d.shape m) s

end H2K5.Door
