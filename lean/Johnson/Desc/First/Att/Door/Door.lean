-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Door.lean: K5's files' filling of the table of joints' door (Johnson/Desc/First/Borders.lean: More { rows, start }): who makes, asks and drops K5's named public items, place by place. Names alone. No Mathlib.
  «K5.readsThere» (seg m): "what the caller's forms will name is there" (its Bool: Johnson/Desc/First/Att/Door/ReadsThereB.lean): at an attention segment: made at piece 1 (the segment's first sending with its opening) · asked and dropped at piece 3 (K5's block). One block (the lookup on the calls, piece 2) owes its keeping.
  «K5.okAt» (seg m): "every slot that what was heard speaks of is filled in the open ledger, which is sized" (its Bool: Johnson/Desc/First/Att/Door/OkThereB.lean): made at piece 3 (K5's block) · kept at 4 | 5 | 6 | 7 · asked and dropped at piece 8 (the batching). Its spender: the link's law's premise hQ (K5Still.lean:107).
  «K5.liveReq» (seg m): "the live request's frame is at this link, in front of a later sending or the closing, and its group was born as the plan says" (its Bool: liveReqB, Johnson/Desc/First/Att/K05DoorB.lean): made at piece 1 · asked and dropped at piece 3.
  «K5.plain» (seg m): "no start of a heard sumcheck names an entry, and the array of the reads is in the ledger, at least as wide as the plan says" (its Bool: Johnson/Desc/First/Att/Door/PlainThereB.lean): made at piece 3 (K5's block) · kept at 4 | 5 | 6 | 7 · asked and dropped at piece 8 (the batching): «K5.okAt»'s very span. Its spender: the segment's law's premise that every entry which K5's forms name is an entry of row 0 of the array of the reads.
  `moreSeats`: apart: at piece 3 K5's row asks «K12.seatsCarried» and «K12.msgShapes» (K12's; no segment).
  `more`: all four. `moreReads`, `moreOk`, `moreLive`, `morePlain`: each alone.
That the makers can make them is shown by nothing here. «Made at piece 1» is a reading: the walk's print settles it: if the Bool is false at the border behind piece 1 the maker is a later block.
-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First

/-- At an attention segment's piece: a row; elsewhere nothing. -/
def atAtt (f : Nat → Nat → MoreRow) (links : List ModelPart) (p : Place) : MoreRow :=
  match p.link with
  | some m => if links[m]? == some .attention then f m p.piece else {}
  | none => {}

def moreReads : More where
  rows := atAtt fun m k =>
    if k == 1 then { makes := [(some m, "K5.readsThere")] }
    else if k == 3 then { asks := [(some m, "K5.readsThere")], drops := [(some m, "K5.readsThere")] }
    else {}

def moreOk : More where
  rows := atAtt fun m k =>
    if k == 3 then { makes := [(some m, "K5.okAt")] }
    else if k == 8 then { asks := [(some m, "K5.okAt")], drops := [(some m, "K5.okAt")] }
    else {}

def moreLive : More where
  rows := atAtt fun m k =>
    if k == 1 then { makes := [(some m, "K5.liveReq")] }
    else if k == 3 then { asks := [(some m, "K5.liveReq")], drops := [(some m, "K5.liveReq")] }
    else {}

def morePlain : More where
  rows := atAtt fun m k =>
    if k == 3 then { makes := [(some m, "K5.plain")] }
    else if k == 8 then { asks := [(some m, "K5.plain")], drops := [(some m, "K5.plain")] }
    else {}

/-- Apart, not in `more`: K5's row's asks of K12's two items «K12.seatsCarried» and «K12.msgShapes» (no segment), which K5's law spends at piece 3 (the ask is laid in K5's own More, meant so that pubFit guards it). To be merged only together with K12's rows: alone pubFit rings: asked, and made by nobody. -/
def moreSeats : More where
  rows := atAtt fun _ k =>
    if k == 3 then { asks := [(none, "K12.seatsCarried"), (none, "K12.msgShapes")] } else {}

/-- **K5's files' filling.** -/
def more : More := ((moreReads.merge moreOk).merge moreLive).merge morePlain

/-- Is the item of that name open, at whichever segment? -/
def isOpen (name : String) (Q : List Pub) : Bool :=
  Q.any fun q => match q with | .more _ n => n == name | _ => false

end H2K5.Door
