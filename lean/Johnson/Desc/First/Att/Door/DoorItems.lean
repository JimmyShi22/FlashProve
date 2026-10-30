-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/DoorItems.lean: for a file of evaluations along a walk: K5's files' offered fillings of the table of joints' public items at an attention segment, each a Bool on the first chain's record alone: so that a walk over a stored proof can evaluate them at every border at which the item is open, and pubHeld whole at K5's two borders. No Mathlib; no separate root.
It imports: the table (Johnson/Desc/First/Borders.lean) · the lookups' two Bools (Johnson/Desc/First/Look/K3Borders.lean: sizedB · k3OnIn · k3OnOut) · the lookups' parameters off the public record (Look/LookKind.lean: placeAt) · Johnson/Desc/First/Att/Door/ReadsThereB.lean · Johnson/Desc/First/Att/Door/DoorBools.lean · Johnson/Desc/First/Att/Door/OkThereB.lean · Johnson/Desc/First/Att/GeoOf.lean · Johnson/Desc/First/Att/Door/Door.lean.
The letters that the file of evaluations hands in: links: the table's own list of links · W: the public record · arrOf l: the plan's list of arrays of link l (the built link's arrayOf) · ownOf l: the seats that a form may read in front of the second sending (by report: Numbers.sent l 0).
  offerK5 links W arrOf ownOf q s : Option Bool: the item's Bool at s where one is offered here; none elsewhere (another kind's item, or a layers' | the head's segment). At an attention link an offer never falls away in silence (of the items that read W; K5.liveReq reads the letter shape alone): where the public record has no plan, place or shape the item is false (by reading alone).
      ledger m: the open ledger is sized · lookIn m 2 | lookOut m 2 | lookOut m 7: the lookups' own two Bools at the calls' | the digits' parameters · callerIn m: nothing is heard at K5's seat, the lookup's return is held, next is the plan's (the calls' first slot + the lookup's scalars) · lookIn m 7: k3OnIn at the digits' parameters, and the link's number and list of arrays are the plan's · freeAbove m: the ledger has the plan's number of slots and every slot from next on is free · linkFresh m: nothing is heard at the digits' seat and the link's list of arrays is the plan's · more (some m) "K5.readsThere": readsThereB · more (some m) "K5.okAt": okThereB at the geometry of the plan of the segment's group (Johnson/Desc/First/Att/Door/OkThereB.lean).
      · look m: lookAttB (Johnson/Desc/First/Att/Door/PubK5.lean).
      Not offered here: left m | leftOn m (their content is a Prop: pubP).
  One item more of K5's own: more (some m) "K5.plain" (Johnson/Desc/First/Att/Door/PlainThereB.lean).
  «K5.shapesAt» is no item (another kind's «K12.msgShapes» is that sentence's name): its Bool is K5's law's letter shapesLetterB (Johnson/Desc/First/Att/Door/PubK5.lean); lettersK5: the two letters, for the walk to print beside · look m has a control (its slots' bound as a letter: lookAttUpTo) · that offerK5's arms at K5's own items are pubK5's:
  no theorem of this library says it.
  One item more of K5's own: more (some m) "K5.liveReq" (Johnson/Desc/First/Att/K05DoorB.lean); one letter more: shape (the request's shape): offerK5 links W arrOf ownOf shape q s.
  By the rule of the table's files the owner of an item lays it: K5's are callerIn | look at attention · K5.readsThere · K5.okAt: they are laid by K5's layer (Johnson/Desc/First/Att/Door/PubK5.lean: pubK5; Johnson/Desc/First/Att/Door/FillK5.lean: fillK5). ledger · freeAbove (the table's files') · lookIn · lookOut · linkFresh (the lookups') stand here as K5's laws' letters, for the walk to print beside the owners' Bools.
  controlsK5: three fillings that are wrong on purpose, each with the items that are due false.
  heldK5 …  Q s: of the open items Q: how many are offered here · how many of these are true · the names of the false.
-/
import Johnson.Desc.First.Look.K3Borders
import Johnson.Desc.First.Look.LookKind
import Johnson.Desc.First.Att.Door.ReadsThereB
import Johnson.Desc.First.Att.Door.DoorBools
import Johnson.Desc.First.Att.Door.OkThereB
import Johnson.Desc.First.Att.Door.PubK5
import Johnson.Desc.First.Att.GeoOf
import Johnson.Desc.First.Att.Door.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K3 (k3OnIn k3OnOut)

/-- Is link m an attention segment? BY THE TABLE's OWN LIST OF LINKS: the test of Door.lean's rows. -/
def isAtt (links : List ModelPart) (m : Nat) : Bool := links[m]? == some .attention

/-- The item's Bool, where we offer one, WITH THREE OF THE PLAN's NUMBERS (the caller's first slot; the ledger's number of slots; the number of heads, and so of pairs) SHIFTED BY d: d = 0: the offered filling; d = 1: a control. -/
def offerK5By (d : Nat) (links : List ModelPart) (W : Verify.Public) (arrOf : Nat → Array (Nat × String)) (ownOf : Nat → List (Nat × Nat))
    (shape : Params.ReqShape) (q : Pub) (s : S) : Option Bool :=
  -- AT AN ATTENTION LINK AN OFFER NEVER FALLS AWAY: where the public record has no plan, no place or no shape the item is FALSE (of the items that read W)
  let at_ (m : Nat) (b : Option Bool) : Option Bool := if isAtt links m then some (b.getD false) else none
  match q with
  | .ledger m => at_ m (some (s.fork?.any VerifiableInference.Desc.K3.sizedB))
  | .lookIn m 2 => at_ m ((Look.placeAt W m false).map fun pC => k3OnIn pC s)
  | .lookOut m 2 => at_ m ((Look.placeAt W m false).map fun pC => k3OnOut pC s)
  | .lookOut m 7 => at_ m ((Look.placeAt W m true).map fun pD => k3OnOut pD s)
  | .callerIn m => at_ m ((Look.placeAt W m false).bind fun pC => pC.shape.map fun hC =>
      callerIn3B (pC.first + Forest.elems hC + d) s)
  | .lookIn m 7 => at_ m ((Look.placeAt W m true).map fun pD =>
      k3OnIn pD s && s.link?.any fun L => L.link == pD.link && L.arrayOf == arrOf m)
  | .freeAbove m => at_ m ((W.A[m / 2]?).map fun a => freeAboveB (a.ns + d) s)
  | .linkFresh m => at_ m (some (linkFreshB (arrOf m) s))
  | .look m => at_ m (some (lookAttUpTo (fun F => if d == 0 then F.ns else 0) s))
  | .more (some m) "K5.readsThere" => at_ m (some (readsThereB W (ownOf m) s))
  | .more (some m) "K5.okAt" => at_ m ((W.A[m / 2]?).map fun a =>
      okThereB { Att.P.geoOf a.S with HA := (Att.P.geoOf a.S).HA + d } s)
  | .more (some m) "K5.plain" => at_ m ((W.A[m / 2]?).map fun a => plainThereB (if d == 0 then a.iU3 else s.fork?.elim 0 (·.trees.size)) a.nW s)
  | .more (some m) "K5.liveReq" => at_ m (some (Att.P.liveReqB
      (if d == 0 then bornOf shape m else (bornOf shape m).push (0, 0)) s))
  | _ => none

/-- **The item's Bool, where we offer one.** -/
def offerK5 := offerK5By 0

/-- THREE CONTROLS, each a filling that is wrong on purpose; behind each name: the items that are DUE FALSE wherever they are open (all others as at offerK5). -/
def controlsK5 (links : List ModelPart) (W : Verify.Public) (arrOf : Nat → Array (Nat × String)) (ownOf : Nat → List (Nat × Nat))
    (shape : Params.ReqShape) :
    List (String × (Pub → S → Option Bool)) :=
  [("the plan's numbers + 1 (born: one pair more): DUE FALSE: callerIn · freeAbove · K5.okAt · K5.liveReq · K5.plain (an array's number beyond the ledger's arrays) · look (its slots' bound 0: where the last claim's form names a slot)", offerK5By 1 links W arrOf ownOf shape),
   ("every link's list of arrays empty: DUE FALSE: linkFresh · lookIn m 7", offerK5By 0 links W (fun _ => #[]) ownOf shape),
   ("no seat may be read: DUE FALSE: K5.readsThere", offerK5By 0 links W arrOf (fun _ => []) shape)]

/-- K5's LAWS' TWO LETTERS FOR K12's TWO ITEMS, at attention link m: name · the Bool · a control that is due false (one kept message more) · the letter's list's length. To be printed wherever «K5.liveReq» is open. -/
def lettersK5 (d : K5Data) (m : Nat) (s : S) : List (String × Bool × Bool × Nat) :=
  [("seatsAtB, for K12.seatsCarried (with membersHeld)", seatsLetterB d m s,
      Att.P.seatsAtB ((keptOf d.shape m).length + 1) (d.seatsOf m) (d.ownOf m) s, (d.seatsOf m).length),
   ("shapesAtB, for K12.msgShapes", shapesLetterB d m s, shapesLetterB d m s 1, (shapesOf d.shape m).length)]

/-- Of the open items: offered · true · the false ones. -/
def heldK5 (links : List ModelPart) (W : Verify.Public) (arrOf : Nat → Array (Nat × String)) (ownOf : Nat → List (Nat × Nat))
    (shape : Params.ReqShape) (Q : List Pub) (s : S) : Nat × Nat × List Pub :=
  let off := Q.filterMap fun q => (offerK5 links W arrOf ownOf shape q s).map fun b => (q, b)
  (off.length, (off.filter (·.2)).length, (off.filter fun x => !x.2).map (·.1))

end H2K5.Door
