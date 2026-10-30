-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean: the proof file's description, assembled from blocks that other
modules supply. No file of this folder that it imports wraps a step of `verify-on-bytes` into a
block. `verify-on-bytes`'s modules are among its imports (through Pub.lean and Ground.lean);
which constants the description reaches is not shown here (see OnlineDescription.lean).
  `onlineDescriptionFromBlockTables`   the description, from the three public files: the public part (Pub.lean: `Road`),
                 then `onlineDescriptionFromPublicPart`. The blocks are arguments, so this file imports none of the modules
                 that supply them; OnlineDescription.lean passes them in.
  `onlineDescriptionFromPublicPart`        the description, from the public part and a `PureSeat`. The first chain is put
                 together place by place (Places.lean: `spotsOf`), at the state `S` itself; the
                 two later chains come whole.
  `faultsAt`, `lackingAt`   the two tests that `onlineDescriptionFromPublicPart` asks first. Each answers in words.
Terms. Block, kind, chain, segment, place, state, claim and batching: see the head of
Johnson/Desc/First/Driver/Chain.lean ("the driver"). A segment is a `Link` of Block.lean.
`verify-on-bytes`, under OnBytes/, was translated by hand from the C++ source. A lot (`Lot`,
LotCore.lean) is a named table of blocks from one module. A segment's gatherer is the function that
`Link.blocksInOrder` hands its batching: it runs the lists of claims that the segment's blocks state. Other
terms: lean/GLOSSARY.md.
Words in refusals. "link": a segment. "table of blocks": a lot. "the batching as a function": of
the segment's gatherer. "laid", "opened", "cleared": a segment's three blocks of the kind `frame`.

Which block is used. At each place, a block of a lot that says of itself that its blocks do not
depend on the request (`letters := false`) and that at that place they run no step of
`verify-on-bytes` (`still`). So whether a description is returned rests on the lots' own statements
`letters` and `still`, and on `standIns` for the two later chains.

When `onlineDescriptionFromPublicPart` refuses. If the places, the shape or the segments' records cannot be computed
(`baseOf`); if the blocks are inconsistent (`faultsAt`); if something is missing (`lackingAt`, which
names everything that is missing at once); or if the driver does not accept the blocks (`chainBy`).
Where a part is missing, `chainBy` (Frames1.lean), `fill` (FillCore.lean) and `partsAt` fall back on
something that tests nothing. `lackingAt` keeps these cases out of the description: a missing part
would otherwise weaken it silently. For every segment it asks for
  * the blocks for its start and for its end, and, where its first place holds `verify-on-bytes`'s
    step that enters the segment (not in the head's segment), the block for what follows that
    place;
  * the batching as a function of the segment's gatherer. Without it `fill` would hand the gatherer
    to a block that ignores it, and the claims that the segment's blocks state would be added by
    nobody;
  * `Link.each` and `Link.tests`.
The chain's first block is the exception: no lot of OnlineDescriptionBlocks.lean supplies one, and a block that
tests nothing stands there by intent. The tests on the chain's public parameters are asked while the
public part is computed (`pubBy`, Pub.lean) and in `fileOk` (Frames1.lean), not in that block.

-/
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.ProofFile.Whose

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First

/-- What a description is assembled from. -/
structure PureSeat where
  /-- what computes the segments' records, for `blankBy` and for the tests on the instance -/
  links : LinksBy
  lots : List Lot
  shared : Option SharedSeat
  second : Option SecondSeat
  /-- the test of the guard on the reply (Frames1.lean: `sameReply`). It is a field so that a test
  harness can run the same blocks with a guard that does nothing; the description keeps the default
  -/
  same : S → S → Bool := sameReply
  /-- stands for the second hash function (Pub.lean: `SecondHashFunctionArgument`); used for the request's item in
  the tests on the instance. No default: the caller supplies it -/
  older : SecondHashFunctionArgument

/-- What the first chain is put together from. `places`: for each place its block, or why there is
none. `frames`: the blocks of the kind `frame`, with their roles. -/
structure PureParts where
  places : List (Spot × Except String (Block S Cl))
  frames : List (FrameRole × Block S Cl)
  /-- FillCore.lean's `Gather`, from the lots' fields `batch`, `each` and `tests` -/
  road : Gather S Cl
  /-- the segments for which a lot supplies the batching as a function of the gatherer -/
  onRoad : List Nat := []
  /-- the segments for which a lot supplies `Link.each`, and those for which one supplies
  `Link.tests` -/
  eachAt : List Nat := []
  testsAt : List Nat := []

/-- The blocks at the places, in order; the first reason where one is missing. -/
def PureParts.base (P : PureParts) : Except String (List (Block S Cl)) :=
  P.places.mapM fun (x : Spot × Except String (Block S Cl)) => x.2

/-- The roles of the blocks of the kind `frame`. -/
def PureParts.roles (P : PureParts) : List FrameRole :=
  P.frames.map fun (x : FrameRole × Block S Cl) => x.1

/-- What `faultsAt`, `partsAt` and `lackingAt` all need, computed once: the places, the shape of the
first chain, the segments' records without a request, and every lot's blocks at these. -/
structure PureBase where
  spots : List Spot
  shape : List (String × Place)
  G₀ : Ground
  all : List (Lot × List (Block S Cl))
  /-- for each segment, the one place at which the driver asks for the batching as a function of the
  gatherer: `a9` in `linkAt` (Johnson/Desc/First/Driver/Chain.lean). A segment has three places of
  the kind K9; at the two others the driver asks for a block -/
  batchAt : List (Nat × Place)

/-- It refuses if the places, the shape or the segments' records cannot be computed, in that order.
-/
def baseOf (Z : Pub) (T : PureSeat) : Except String PureBase :=
  -- `Except.bind` is written out: `PureBase` holds lots, and so lives one universe higher.
  (orSay "the table of steps names a kind that is not known" (spotsOf Z.cuts)).bind fun ps =>
  (shapeOf Z).bind fun sh =>
  (orSay "the links' records for a request of zeros cannot be computed"
    (blankBy T.links Z)).bind fun G =>
    .ok { spots := ps, shape := sh, G₀ := G, all := T.lots.map fun L => (L, L.blocks G)
          batchAt := (subsOf Z).zipIdx.map fun x =>
            (x.2, ⟨1, some x.2, (kindsBeforeBatching x.1 (x.2 == 0)).length + 1, KindName.K9⟩) }

/-- What the first chain is put together from. -/
def partsAt (T : PureSeat) (B : PureBase) : PureParts :=
  let spots := B.spots
  let shape := B.shape
  let G₀ := B.G₀
  let all := B.all
  -- Only lots whose blocks do not depend on the request count. Where a lot supplies the batching as
  -- a function, the list of places holds that function at a gatherer that gathers nothing, for the
  -- block's name and data. The chain itself takes the function, through `road`.
  let quiet := T.lots.filter fun L => !L.letters
  let maker := fun (a : Place) => quiet.findSome? fun L => L.batch G₀ a
  let nameAt := fun (a : Place) (n : String) =>
    ((spots.find? fun p => p.place == a).map fun p => p.name).getD n
  let road : Gather S Cl :=
    { batch := fun a => (maker a).map fun mk g =>
        let b := mk g
        { guardMark b with name := nameAt a b.name }
      -- The driver's record needs a function for every number. Where no lot supplies one, a test
      -- that always passes is written. For a segment of the plan that case is not reached in a
      -- description that `onlineDescriptionFromPublicPart` returns: `lackingAt` refuses first.
      each := fun l =>
        match quiet.findSome? fun L => L.each G₀ l with
        | some f => f
        | none => fun _ _ _ => .ok ()
      tests := fun l =>
        match quiet.findSome? fun L => L.tests G₀ l with
        | some f => f
        | none => fun _ => .ok ()
      same := T.same }
  -- Looked up at the place at which the driver asks, not at any place of the kind K9.
  let onRoad := B.batchAt.filterMap fun x => if (maker x.2).isSome then some x.1 else none
  let links := (spots.filterMap fun p => p.place.link).eraseDups
  let eachAt := links.filter fun l => (quiet.findSome? fun L => L.each G₀ l).isSome
  let testsAt := links.filter fun l => (quiet.findSome? fun L => L.tests G₀ l).isSome
  let places : List (Spot × Except String (Block S Cl)) := spots.map fun p =>
    -- A lot may spell a step's name in `still` as printouts do or as the table does.
    let looks := p.cuts.flatMap fun c => [stepName c.look, c.look]
    let here := all.filterMap fun x => (x.2.find? fun b => b.place == p.place).map fun b => (x.1, b)
    let face := (road.batch p.place).map fun mk => mk fun s => .ok ([], s)
    let sits := here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains)
    (p, match face, sits with
      | some f, _ => .ok f
      | none, some x => .ok { guardMark x.2 with name := p.name }
      | none, none =>
        match here with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here"))
  let frames : List (FrameRole × Block S Cl) := all.flatMap fun x =>
    if x.1.letters then []
    else (x.2.filter fun b => b.place.kind == KindName.frame).filterMap fun b =>
      match roleOf shape b.place with
      | .common => none
      | .stray => none
      | r => some (r, guardMark b)
  { places := places, frames := frames, road := road, onRoad := onRoad, eachAt := eachAt
    testsAt := testsAt }

/-- `baseOf`, then `partsAt`. -/
def partsOf (Z : Pub) (T : PureSeat) : Except String PureParts :=
  (baseOf Z T).bind fun B => .ok (partsAt T B)

/-- What is wrong with the lots' blocks, in words; empty if nothing is. All blocks of all lots are
looked at, whether they would be used or not: two blocks at one place are a fault whichever of them
would be used. -/
def faultsAt (T : PureSeat) (B : PureBase) : List String :=
  let shape := B.shape
  let G₀ := B.G₀
  let spots := B.spots
  let blocks := B.all.flatMap fun x => x.2
  let many := fun (f : Lot → Bool) => decide (1 < (T.lots.filter f).length)
  -- The batching as a function: supplied at a place at which the driver does not ask for it; making
  -- a block that bears another place (tested at a gatherer that gathers nothing); supplied by two
  -- lots; by a lot whose blocks depend on the request; or at a place where there is also a block.
  let atPlaces := spots.flatMap fun p =>
    let gives := T.lots.filter fun L => (L.batch G₀ p.place).isSome
    (if gives.isEmpty then []
     else
      (if !(B.batchAt.any fun x => x.2 == p.place) then
        ["the batching is supplied as a function at " ++ p.name ++
          ", where the driver does not ask for it"]
       else []) ++
      (if gives.any fun L =>
          ((L.batch G₀ p.place).map fun mk => (mk fun s => .ok ([], s)).place != p.place).getD false
        then ["the batching that is supplied as a function at " ++ p.name ++
          " makes a block that bears another place"]
       else []) ++
      (if 1 < gives.length then
        ["two tables of blocks supply the batching as a function at " ++ p.name] else []) ++
      (if gives.any (·.letters) then
        ["a table that says it depends on the request supplies the batching as a function at " ++
          p.name]
       else []) ++
      (if blocks.any fun b => b.place == p.place then
        ["the place " ++ p.name ++ " has both a block and the batching as a function"] else []))
  let onRoad := B.batchAt.filterMap fun x =>
    if T.lots.any fun L => (L.batch G₀ x.2).isSome then some x.1 else none
  -- At the batching's place the chain takes the function, not the block of the list. What
  -- `chainBy` joins after the block of that name would silently end up nowhere.
  let batchNames := spots.filterMap fun p =>
    if B.batchAt.any fun x => x.2 == p.place then some p.name else none
  let joined := (blocks.filter fun b => b.place.kind == KindName.frame).filterMap fun b =>
    match roleOf shape b.place with
    | .behind _ n =>
      if batchNames.contains n then
        some ("the block " ++ b.name ++ " would be joined after the batching at " ++ n ++
          ": it would end up in no chain")
      else none
    | _ => none
  let atLinks := ((spots.filterMap fun p => p.place.link).eraseDups).flatMap fun l =>
    (if many fun L => (L.each G₀ l).isSome then
      [s!"two tables of blocks supply Link.each for link {l}"]
     else []) ++
    -- Without the function the gatherer is ignored, and `Link.each` with it.
    (if !onRoad.contains l && T.lots.any fun L => (L.each G₀ l).isSome then
      [s!"Link.each is supplied for link {l}, which has no batching as a function: it is idle"]
     else []) ++
    (if many fun L => (L.tests G₀ l).isSome then
      [s!"two tables of blocks supply Link.tests for link {l}"]
     else [])
  -- Blocks are joined, and left-over blocks are found, by name: so no two blocks of the chain may
  -- bear one name.
  let names := shape.map (·.1)
  let twice := (names.filter fun n => 1 < names.count n).eraseDups.map fun n =>
    "two places bear the name " ++ n
  faultsOf shape blocks ++ twice ++ atPlaces ++ joined ++ atLinks

/-- `baseOf`, then `faultsAt`. -/
def pureFaults (Z : Pub) (T : PureSeat) : Except String (List String) :=
  (baseOf Z T).bind fun B => .ok (faultsAt T B)

/-- What is missing, in words; empty if nothing is. The head of this file says what is asked and
why. -/
def lackingAt (T : PureSeat) (P : PureParts) : List String :=
  let links := (P.places.filterMap fun x => x.1.place.link).eraseDups
  let first := P.places.filterMap fun x =>
    match x.2 with
    | .ok _ => none
    | .error why =>
      some (s!"{x.1.name} ({kindWord x.1.place.kind})" ++ (if why.isEmpty then "" else ": " ++ why))
  -- Three blocks of the kind `frame` for each segment: for its start, for what follows its first
  -- place, and for its end. Where `chainBy` finds none for the start or the end, it passes the
  -- state on untested.
  let roles := P.frames.map (·.1)
  let firstAt := fun (l : Nat) =>
    (P.places.find? fun x => x.1.place.link == some l && x.1.place.piece == 1).map (·.1.name)
  let has := fun (r : FrameRole) => roles.contains r
  -- The second of the three is asked for only where the segment's first place holds
  -- `verify-on-bytes`'s step that enters the segment. In the head's segment it does not.
  let enters := fun (l : Nat) => P.places.any fun x =>
    x.1.place.link == some l && x.1.place.piece == 1 && x.1.cuts.any fun c => isFrameStep x.1 c.look
  let opened := fun (l : Nat) =>
    !enters l ||
      match firstAt l with
      | some n => has (.behind l n)
      | none => false
  let frames := links.flatMap fun l =>
    (if has (.lay l) then [] else [s!"link {l}: laid (frame)"]) ++
    (if opened l then [] else [s!"link {l}: opened (frame)"]) ++
    (if has (.clear l) then [] else [s!"link {l}: cleared (frame)"]) ++
    (if P.onRoad.contains l then [] else [s!"link {l}: the batching as a function (K9)"]) ++
    (if P.eachAt.contains l then [] else [s!"link {l}: Link.each (K9)"]) ++
    (if P.testsAt.contains l then [] else [s!"link {l}: Link.tests (K9)"])
  let later := fun (what : String) (lot : Option (String × List String)) =>
    match lot with
    | none => [what ++ " (the whole chain)"]
    | some x => x.2.map fun n =>
      s!"{n} ({what}: still runs the older verifier, by the statement of {x.1})"
  first ++ frames ++ later "the shared chain" (T.shared.map fun A => (A.lot, A.standIns)) ++
    later "the second chain" (T.second.map fun B => (B.lot, B.standIns))

/-- `partsOf`, then `lackingAt`. -/
def lackingOf (Z : Pub) (T : PureSeat) : Except String (List String) :=
  (partsOf Z T).map (lackingAt T)

/-- The description, once `faultsAt` and `lackingAt` have found nothing. -/
def onlineDescriptionAfterTests (Z : Pub) (T : PureSeat) (P : PureParts) : Except String (FileDescription Inst) :=
  -- `Except.bind` is written out: `FileDescription` lives one universe higher than what is bound here.
        P.base.bind fun base =>
          (chainBy Z base P.frames P.road).bind fun c =>
            match T.shared, T.second with
            | some A, some B =>
              .ok (fileDescBy T.older T.links Z A B (fun s => s) (startS Z) c)
            | _, _ => .error "no description: nothing usable is supplied for: a later chain"

/-- **The description**, from the public part and a `PureSeat`. The lots' blocks are computed once
(`baseOf`). That the value is the same as if `pureFaults`, `lackingOf` and `partsOf` were asked one
after the other is `pureZ_thrice` (Law/PureZOnce.lean). -/
def onlineDescriptionFromPublicPart (Z : Pub) (T : PureSeat) : Except String (FileDescription Inst) :=
  (baseOf Z T).bind fun B =>
    let faults := faultsAt T B
    let P := partsAt T B
    let lack := lackingAt T P
    if !faults.isEmpty then
      .error ("no description: the supplied blocks are inconsistent: " ++ "; ".intercalate faults)
    else if !lack.isEmpty then
      .error ("no description: nothing usable is supplied for: " ++ ", ".intercalate lack)
    else onlineDescriptionAfterTests Z T P

/-- **The description, from the three public files** (policy.txt, layout.txt, KL.bin). The lots and
the two later chains are passed in as functions of the public part. `o` stands for the format's
second hash function. -/
def onlineDescriptionFromBlockTables (o : SecondHashFunctionArgument) (R : Road) (lots : Pub → List Lot)
    (shared : Pub → Option SharedSeat) (second : Pub → Option SecondSeat)
    (pol lay KL : ByteArray) : Except String (FileDescription Inst) :=
  (R.pub o pol lay KL).bind fun Z =>
    onlineDescriptionFromPublicPart Z { links := R.links, lots := lots Z, shared := shared Z, second := second Z
                                        older := o }

end ProofFile
