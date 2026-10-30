-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Lot.lean: the honest side of the kind "lookup" (K3): where its rows
stand in a proof file's first chain, and the entry under which they enter it. Definitions with code,
tests by evaluation at synthetic lists, and one theorem by rfl (the lot's name).

Terms. Honest/K3/GLOSSARY.md ("site", "lot", "place, piece", "caller", "base", "half"). In this
file: every link of the first chain has two lookups: one on its calls, one on the digits of its
smallness test. The description's sub-protocols at these places come out of one lot (`K3Lot.lot`,
Johnson/Desc/ProofFile/Lot/K3.lean). This file goes over that lot's own list of addresses
(`K3Lot.addresses`) and makes, of the public part alone, what a row needs to know of its place.

What is defined and shown.
  1 `Caller`, `callerOf`: who calls the lookup at a link: the layers, attention or the head; and its
    number among its like.
  2 `spotRounds`, `baseIn`, `rngIn`: how many rounds of the chain stand in front of a place, off the
    chain's table of places (`spotsOf`, Johnson/Desc/ProofFile/Places.lean); the number of the round
    that samples the matrix of a link's smallness test.
  3 `Site`, `siteAt`, `lookSites`, `lookAts`, `lookMisses`: a lookup's public data at its place; all
    of a public part's; the addresses at which none could be made, in words.
  4 `lotName`, `lotName_is`, `lotBy`, `seatRow`, `lotBySeat`: the lot's honest side (`HLot`,
    Honest/Frame.lean): general in the row; and at a row that is typed at a small structure, seated
    by `Part.lift`.
  5 `idlePart`, `idleRow`: a stand-in for a row: the right numbers of parts and rounds, nothing
    sent: for the tests on numbers alone.
  6 `siteTests`, `lotTests`, `failing`, `siteLine`: the tests against a description's own
    sub-protocols, each with its name; a site in one printed line.
  7 Tests of all this at synthetic lists.

What is the verifier's own, by name: the addresses (`K3Lot.addresses`, and in it `K3.pieceAt`: 2 and
7, at the head 3 and 8); the place's parameters (`First.Look.placeAt`); the shape (`P.shape`); the
face (`K3.faceOf`). These are the terms at which the hearing `K3.Law.hearVia`
(Johnson/Desc/First/Look/Via/Via.lean) is called.

What is written a second time here, and what tests it.
  `Caller` has, case for case, the three cases of the library's `ModelPart`
    (Johnson/Desc/First/Driver/Chain.lean); no function and no lemma of this file leads from the one
    type to the other. Honest/K3/Law/TiesSealedLot.lean [not in this library] has the map (`subOf`),
    and that `callerOf` at two and at twelve groups, with attention links, tells the library's
    written lists `linksFive` and `linksTwentyFive` (`callerOf_five`, `callerOf_twentyFive`).
  `callerOf` repeats the split of the links' numbers in `First.Look.lookAt`
    (Johnson/Desc/First/Look/LookAt.lean). `siteTests` compares it with the word that `lookAt` puts
    into the place's name.
  The number of rounds in front is added up off the table of places, since a lot's honest side is
    handed the public part and the segments' structures and no description. `siteTests` compares it
    with `roundsInFront` (Honest/ForKinds.lean) on the description's own list of sub-protocols.
  The round that samples a smallness test's matrix is found by its place's kind (K8) in the same
    table. `siteTests` compares its number with the description's own list: just one sub-protocol of
    the link stands behind so many rounds and has one round, named "RNG", which samples matrix
    entries.
  `lotName`: `HLot.name` is a string and the lot is a function of the public part; `lotName_is` ties
    the two at every public part.

How the tests can fail. Section 7 shows them failing at alterations: all eight tests on the lot, and
ten of the thirteen on a site; "a block stands at the place", "the face passes the hearing's test on
its numbers" and "a half stands at the place" are never seen to reject in this file. The
alterations: a sub-protocol with
one round more, another cut, a sub-protocol in front with one round more, a half at a place without
a sub-protocol, two halves at one place, a lookup's sub-protocol without a half, another caller's
word, another lot's name, a shape of one call, nothing at all, the matrix's round under another
name, without a matrix entry, at another number, lacking, or named at the calls.

Imported. Beneath this file lie Honest/Frame.lean,
Honest/ForKinds.lean, Honest/BookOf.lean (imported by a line of this
file's own),
Honest/Side.lean and Honest/Sum.lean.

Limits. Where the public structure gives no place, no shape, or the table has no such place (at the
digits: or not just one round that samples the matrix), no site is made and no half stands there:
`lookMisses` says so in words, and `lotTests` counts. The tests of section 6 are functions: they
show something only where a program evaluates them at a description; this file evaluates them at
synthetic lists alone. That a site's face is the face at which the sub-protocol at its place hears
is read off the texts named above and is not proved here. Shown in part: Honest/K3/Law/SitesOk.lean
(`sites_shape_ok`): a site's face is the face of its shape; and Honest/K3/LotLaw.lean (`hear_site`):
the lot's sub-protocol there has the rounds of the site's own parameters. That the sub-protocol
hears at that face is still read off the texts. `idleRow` sends nothing and is no prover's row. The
segments' structures (`Ground`) are not read.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages
import Johnson.Desc.ProofFile.Honest.BookOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open VerifiableInference.Desc (Block Place roundlessBlock)

/-! ## 1 Who calls -/

/-- Whose link a lookup stands in. -/
inductive Caller where
  | layers
  | attention
  | head
  deriving DecidableEq, Repr

/-- The word that `First.Look.lookAt` puts into a place's name for it. -/
def Caller.word : Caller → String
  | .layers => "layers"
  | .attention => "attention"
  | .head => "head"

/-- **Whose link number i is, and its number among its like**, from 0. Here p4 says that attention
links stand between the layers' links, and groups is the number of groups of layers (the fields p4
and NGr of `Verify.Public`). The head's link is the last; a number beyond it is not told apart here:
no place is made there. -/
def callerOf (p4 : Bool) (groups i : Nat) : Caller × Nat :=
  let step := if p4 then 2 else 1
  if i == step * groups then (.head, 0)
  else if i % step == 0 then (.layers, i / step)
  else (.attention, i / step)

/-! ## 2 The rounds in front -/

/-- The rounds of a place, by the table of places. -/
def spotRounds (p : Spot) : Nat := p.cuts.foldl (fun n c => n + c.take) 0

/-- **How many rounds stand in front of the place a**, by a table of places; nothing if the table
has no such place. -/
def baseIn (ps : List Spot) (a : Place) : Option Nat :=
  if ps.any (·.place == a) then
    some ((ps.takeWhile (·.place != a)).foldl (fun n p => n + spotRounds p) 0)
  else none

/-- **The number, among the chain's rounds, of the round that samples the matrix of link i's
smallness test**: the one round of the link's one place of the kind K8; nothing unless the table has
just one such place and it has just one round. -/
def rngIn (ps : List Spot) (i : Nat) : Option Nat :=
  match ps.filter fun p => p.place.link == some i && p.place.kind == .K8 with
  | [p] => if spotRounds p == 1 then baseIn ps p.place else none
  | _ => none

/-! ## 3 A lookup at its place -/

/-- **A lookup's public data at its place**: what the row reads (at) and what the reader of the
prover's input needs besides. -/
structure Site where
  /-- the link's number in the first chain, from 0: the segment's number -/
  link : Nat
  /-- the lookup on the digits of the smallness test; else the one on the link's calls -/
  digits : Bool
  /-- whose link it is -/
  caller : Caller
  /-- that caller's number among its like, from 0 -/
  group : Nat
  /-- the verifier's own public parameters at the place -/
  p : VerifiableInference.Desc.First.Look.P
  /-- the shape that they fix -/
  shape : OnBytes.Model.Forest.Shape
  /-- place, face, rounds in front -/
  at_ : At
  /-- at the digits: the number, among the chain's rounds, of the round that samples the smallness
  test's matrix, on which the digits depend; at the calls nothing -/
  rng : Option Nat

/-- The site at one address of the lot's list. Here ps is the chain's table of places. -/
def siteAt (X : OnBytes.Model.Verify.Public) (ps : List Spot) (x : Nat × Bool × Place) :
    Option Site :=
  (VerifiableInference.Desc.First.Look.placeAt X x.1 x.2.1).bind fun p =>
    p.shape.bind fun h =>
      (baseIn ps x.2.2).bind fun n =>
        let c := callerOf X.p4 X.NGr x.1
        let s : Site :=
          { link := x.1, digits := x.2.1, caller := c.1, group := c.2, p := p, shape := h
            at_ := ⟨x.2.2, VerifiableInference.Desc.K3.faceOf h, n⟩, rng := none }
        if x.2.1 then (rngIn ps x.1).map fun r => { s with rng := some r } else some s

/-- **All lookups of a public part**, in the lot's own order: link by link, the one on the calls,
then the one on the digits. -/
def lookSites (Z : Pub) : List Site :=
  let ps := (spotsOf Z.cuts).getD []
  (K3Lot.addresses Z).filterMap (siteAt Z.p.X ps)

/-- What the rows read of them. The segments' structures are not read. -/
def lookAts (Z : Pub) (_ : Ground) : List At := (lookSites Z).map (·.at_)

/-- The addresses of the lot's list at which no site could be made, each with the first thing that
lacks. -/
def lookMisses (Z : Pub) : List String :=
  let ps := (spotsOf Z.cuts).getD []
  (K3Lot.addresses Z).filterMap fun x =>
    let at' := s!"link {x.1}, " ++ (if x.2.1 then "digits" else "calls") ++ ": "
    match VerifiableInference.Desc.First.Look.placeAt Z.p.X x.1 x.2.1 with
    | none => some (at' ++ "the public record gives no place")
    | some p =>
      if p.shape.isNone then some (at' ++ "the place's numbers give no shape")
      else if (baseIn ps x.2.2).isNone then some (at' ++ "the table of places has no such place")
      else if x.2.1 && (rngIn ps x.1).isNone then
        some (at' ++ "the table of places has not just one round that draws the matrix")
      else none

/-! ## 4 The lot's honest side -/

/-- The name of the lot out of which the description takes the lookups' sub-protocols. -/
def lotName : String := "K3: the lookups on the calls and on the digits"

/-- It is that lot's name, at every public part. -/
theorem lotName_is (Z : Pub) : (K3Lot.lot Z).name = lotName := rfl

variable {V W X : Type}

/-- **The lot's honest side**, general in the row: at each site the row there. -/
def lotBy (row : Site → List (Part V W X)) : HLot V W X :=
  { name := lotName
    halves := fun Z _ => (lookSites Z).map fun s => ⟨s.at_.place, row s⟩ }

/-- A row that is typed at a small structure W' and hands nothing on, seated in the chain's input:
wit makes the small structure of the input; what the chain's parts hand on stays. The second stop
reads the small structure too. -/
def seatRow {W' : Type} (wit : W → W') (row : List (Part W' W' Unit)) : List (Part W W X) :=
  row.map (Part.lift wit wit (fun _ => ()) fun x _ => x)

/-- **The lot's honest side at a row of the kind's own types.** Here row is a function of the site
(its place, face and rounds in front are in the field at_; the summands may read the shape too), and
wit, a function of the site, goes from the chain's input to the small structure. -/
def lotBySeat {W' : Type} (row : Site → List (Part W' W' Unit)) (wit : Site → W → W') :
    HLot W W X :=
  lotBy fun s => seatRow (wit s) (row s)

/-! ## 5 A stand-in for a row -/

/-- A part of n rounds that sends nothing, takes no coin and never stops. -/
def idlePart (n : Nat) : Part V W X :=
  { takes := ⟨0, 0⟩, spends := [], carries := []
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := List.replicate n ⟨fun _ _ _ => .ok ⟨[], []⟩, fun t => t.own⟩ }

/-- **A stand-in, no prover's row**: a part for each stage, with the stage's number of rounds,
nothing sent. For the tests on numbers where the row itself is not at hand. -/
def idleRow (a : At) : List (Part V W X) := (stages a.face).map fun s => idlePart (s.rounds a.face)

/-! ## 6 The tests against a description's own sub-protocols -/

variable {S Cl : Type}

/-- **The tests at one site**, each with its name. Here bs is the first chain's list of
sub-protocols (`Chain.blocksInOrder`), and h is the half that stands at the site's place, if one does. -/
def siteTests (bs : List (Block S Cl)) (s : Site) (h : Option (Placed V W X)) :
    List (String × Bool) :=
  let f := s.at_.face
  let b := bs.find? fun b => b.place == s.at_.place
  [("a block stands at the place", b.isSome),
   ("the place is chain 1, the site's link, the kind K3",
      s.at_.place.chain == 1 && s.at_.place.link == some s.link && s.at_.place.kind == .K3),
   ("the face passes the hearing's test on its numbers", f.ok),
   ("the shape has several calls, as the seated hearing asks", decide (1 < s.shape.NC)),
   ("the rounds' names are those that the hearing goes by",
      b.map (·.rounds.map (·.entry.name)) ==
        some ((VerifiableInference.Desc.K3.entriesV f).map (·.name))),
   ("the stages' rounds are the book's cut of the block's rounds",
      b.map partsCut == some ((stages f).map (Stage.rounds f))),
   ("the rounds in front are the chain's own count",
      roundsInFront bs s.at_.place == some s.at_.base),
   ("a half stands at the place", h.isSome),
   ("the half has as many rounds as the block",
      h.isSome && h.map (·.rounds) == b.map (·.rounds.length)),
   ("the half is cut as the book cuts",
      h.isSome && h.map (·.parts.map (·.moves.length)) == b.map partsCut),
   ("the caller is the one that the place's name says",
      s.p.name == s!"LINK {s.link} ({s.caller.word}) " ++ (if s.digits then "digits" else "calls")),
   ("at the digits alone a round is named that draws the matrix", s.rng.isSome == s.digits),
   ("that round is the link's, named RNG, draws matrix entries, and stands in front",
      s.rng.all fun r =>
        decide (r < s.at_.base) &&
          (bs.filter fun c => c.place.link == some s.link &&
            roundsInFront bs c.place == some r &&
            c.rounds.map (fun d => (d.entry.name, d.entry.trits != 0)) == [("RNG", true)]).length
            == 1)]

/-- **The tests on the whole lot**, each with its name. Here names are the names of the
description's lots of the first chain; addresses says how many addresses the lookups' lot lists; bs
is the first chain's list of sub-protocols; name and hs are the honest side's name and its halves.
-/
def lotTests (names : List String) (addresses : Nat) (bs : List (Block S Cl)) (sites : List Site)
    (name : String) (hs : List (Placed V W X)) : List (String × Bool) :=
  let mine := bs.filter fun b => b.place.kind == .K3
  [("just one lot of the description bears the name", names.count name == 1),
   ("the lot's list has an address", addresses != 0),
   ("a site at every address of the lot's list", sites.length == addresses),
   ("as many sites as the chain has blocks of the kind", sites.length == mine.length),
   ("a half for each site, in order", hs.map (·.place) == sites.map (·.at_.place)),
   ("no half without a block", (strays bs hs).isEmpty),
   ("no two halves at one place", (twice hs).isEmpty),
   ("no block of the kind that sends something lacks a half", (lacking mine hs).isEmpty)] ++
  sites.flatMap fun s =>
    (siteTests bs s (hs.find? fun h => h.place == s.at_.place)).map fun t =>
      (s!"link {s.link}, " ++ (if s.digits then "digits" else "calls") ++ ": " ++ t.1, t.2)

/-- The names of the tests that reject. -/
def failing (ts : List (String × Bool)) : List String := (ts.filter fun t => !t.2).map (·.1)

/-- A site in one line, for a print. -/
def siteLine (s : Site) : String :=
  let f := s.at_.face
  s!"link {s.link} · {s.caller.word} {s.group} · " ++ (if s.digits then "digits" else "calls") ++
    s!" · place {s.at_.place.chain}.{s.link}.{s.at_.place.piece}" ++
    s!" · rounds in front {s.at_.base}" ++
    s!" · parts {(stages f).length} · rounds {((stages f).map (Stage.rounds f)).sum}" ++
    s!" · keys 2^{f.parts} · table 2^{f.d} · hidden values {f.slots} from the link's number " ++
    s!"{s.p.first} of {s.p.ns}" ++
    (match s.rng with
     | some r => s!" · the matrix is drawn in round {r}"
     | none => "")

/-! ## 7 Tests at synthetic lists -/

namespace LotToy

-- Who calls. With attention links between (p4), three groups: links 0 2 4 are the layers', 1 3 5
-- attention's, 6 the head's. It fails if the step, the head's number or the halving changes.
#guard (List.range 7).map (callerOf true 3) ==
  [(.layers, 0), (.attention, 0), (.layers, 1), (.attention, 1), (.layers, 2), (.attention, 2),
   (.head, 0)]
-- Without: links 0 1 2 are the layers', 3 the head's; no attention link.
#guard (List.range 4).map (callerOf false 3) ==
  [(.layers, 0), (.layers, 1), (.layers, 2), (.head, 0)]

/-- A row of the table of stretches that takes n rounds. -/
def cut (n : Nat) : VerifiableInference.Desc.First.Cut := ⟨"x", "x", 0, "x", n⟩

def pl (link piece : Nat) : Place := ⟨1, some link, piece, .K3⟩

/-- A synthetic table: places of 2 + 1, 0, 5 and 4 rounds. -/
def spots : List Spot :=
  [⟨"a", ⟨1, some 0, 1, .K1⟩, [cut 2, cut 1]⟩, ⟨"b", ⟨1, some 0, 2, .frame⟩, []⟩,
   ⟨"c", pl 0 3, [cut 5]⟩, ⟨"d", pl 1 3, [cut 4]⟩]

-- The rounds in front: all rows of all places in front, none of the place's own. It fails if a
-- place's later rows, a place without a row, or the place itself is counted otherwise.
#guard baseIn spots ⟨1, some 0, 1, .K1⟩ == some 0
#guard baseIn spots (pl 0 3) == some 3
#guard baseIn spots (pl 1 3) == some 8
-- a place that the table does not have: nothing, and not the number of all rounds
#guard baseIn spots (pl 1 4) == none
-- the kind is part of a place
#guard baseIn spots ⟨1, some 0, 3, .K4⟩ == none

/-- The synthetic table with places of the kind K8 put in: one of one round in link 0, behind three
rounds; one of two rounds in link 1; two in link 2. -/
def spots8 : List Spot :=
  spots.take 2 ++ [⟨"r", ⟨1, some 0, 9, .K8⟩, [cut 1]⟩] ++ spots.drop 2 ++
    [⟨"s", ⟨1, some 1, 9, .K8⟩, [cut 2]⟩, ⟨"t", ⟨1, some 2, 1, .K8⟩, [cut 1]⟩,
     ⟨"u", ⟨1, some 2, 2, .K8⟩, [cut 1]⟩]

-- The round that samples the matrix: the one round of the link's one place of the kind. It fails if
-- the link, the kind or the count of rounds in front changes
#guard rngIn spots8 0 == some 3
-- a place of two rounds; two places; none: nothing
#guard rngIn spots8 1 == none
#guard rngIn spots8 2 == none
#guard rngIn spots8 3 == none

/-- A small face: a shift, four places for bits of which three are real, eight keys, two rows. -/
def face : LFace :=
  { shifted := true, mu := 2, planes := 3, parts := [3], d := 1
    orders := fun _ m => (List.range m).reverse, padding := [], leaf := fun _ _ _ => OnBytes.zeroE }

#guard face.ok

/-- A sub-protocol of the kind at a place, with the rounds that the hearing at a face goes by, and k
idle rounds more. -/
def blockAt (a : Place) (f : LFace) (k : Nat := 0) : Block Unit Unit :=
  let es := VerifiableInference.Desc.K3.entriesV f ++
    List.replicate k (VerifiableInference.Desc.K3.drawEntry "LINE" 1)
  { (roundlessBlock "toy" 1 a.link a.piece .ok : Block Unit Unit) with
    place := a, rounds := es.map fun e => { entry := e }, oracles := es.map fun _ => [] }

/-- A sub-protocol of another kind, of n rounds that send nothing. -/
def other (link piece n : Nat) : Block Unit Unit :=
  { (roundlessBlock "in front" 1 (some link) piece .ok : Block Unit Unit) with
    place := ⟨1, some link, piece, .K9⟩
    rounds := List.replicate n { entry := VerifiableInference.Desc.K3.drawEntry "BAT-sigma" 1 }
    oracles := List.replicate n [] }

/-- How many rounds the small face's lookup has. -/
def len : Nat := (VerifiableInference.Desc.K3.entriesV face).length

/-- A sub-protocol of the kind K8: one round under a name, which samples n matrix entries. -/
def draw (link piece : Nat) (name : String) (n : Nat) : Block Unit Unit :=
  { (roundlessBlock "draw" 1 (some link) piece .ok : Block Unit Unit) with
    place := ⟨1, some link, piece, .K8⟩
    rounds := [{ entry := { name := name, trits := n } }], oracles := [[]] }

/-- A synthetic chain: three rounds, a lookup, a sub-protocol without a round, a round, the round
that samples the matrix, a lookup. -/
def chain (k₀ : Nat := 3) (more : Nat := 0) (name : String := "RNG") (n : Nat := 6) :
    List (Block Unit Unit) :=
  [other 0 1 k₀, blockAt (pl 0 2) face more, roundlessBlock "quiet" 1 (some 0) 3 .ok, other 0 4 1,
   draw 0 5 name n, blockAt (pl 0 7) face]

/-- The verifier's parameters at a synthetic place: the name alone is read by the tests. -/
def par (name : String) (digits : Bool) : VerifiableInference.Desc.First.Look.P :=
  { name := name, set := default, link := 0, digits := digits, calls := #[], pub := #[], lid := 0
    first := 0, ns := 0, lm := 0 }

def site (digits : Bool) (base : Nat) (word : String := "layers") : Site :=
  { link := 0, digits := digits, caller := .layers, group := 0
    p := par (s!"LINK 0 ({word}) " ++ if digits then "digits" else "calls") digits
    shape := { NC := 2 }, at_ := ⟨pl 0 (if digits then 7 else 2), face, base⟩
    rng := if digits then some (base - 1) else none }

def sites : List Site := [site false 3, site true (3 + len + 2)]

def halves (ss : List Site) : List (Placed Unit Unit Unit) :=
  ss.map fun s => ⟨s.at_.place, idleRow s.at_⟩

def names : List String := ["the commitments (K1)", lotName, "another"]

/-- The tests that reject, at a chain, sites, a name and halves. -/
def red (bs : List (Block Unit Unit)) (ss : List Site) (name : String := lotName)
    (hs : List (Placed Unit Unit Unit) := halves ss) (addresses : Nat := 2) : List String :=
  failing (lotTests names addresses bs ss name hs)

-- All pass at the synthetic chain; and there are 8 + 2 * 13 tests
#guard red chain sites == []
#guard (lotTests names 2 chain sites lotName (halves sites)).length == 34

-- Each alteration makes its own tests fail, and no other
-- a sub-protocol in front has one round more: both lookups' counts of rounds in front
#guard red (chain 4) sites ==
  ["link 0, calls: the rounds in front are the chain's own count",
   "link 0, digits: the rounds in front are the chain's own count",
   "link 0, digits: that round is the link's, named RNG, draws matrix entries, and stands in front"]
-- the first lookup's sub-protocol has one round more: names, cut, the half's rounds and cut there;
-- the second's rounds in front
#guard red (chain 3 1) sites ==
  ["link 0, calls: the rounds' names are those that the hearing goes by",
   "link 0, calls: the stages' rounds are the book's cut of the block's rounds",
   "link 0, calls: the half has as many rounds as the block",
   "link 0, calls: the half is cut as the book cuts",
   "link 0, digits: the rounds in front are the chain's own count",
   "link 0, digits: that round is the link's, named RNG, draws matrix entries, and stands in front"]
-- the round under another name; a round that samples no matrix entry; another round's number
#guard red (chain 3 0 "BAT-sigma") sites ==
  ["link 0, digits: that round is the link's, named RNG, draws matrix entries, and stands in front"]
#guard red (chain 3 0 "RNG" 0) sites ==
  ["link 0, digits: that round is the link's, named RNG, draws matrix entries, and stands in front"]
#guard red chain [site false 3, { site true (3 + len + 2) with rng := some (3 + len) }] ==
  ["link 0, digits: that round is the link's, named RNG, draws matrix entries, and stands in front"]
-- no round named at the digits; one named at the calls (round 0 is no RNG)
#guard red chain [site false 3, { site true (3 + len + 2) with rng := none }] ==
  ["link 0, digits: at the digits alone a round is named that draws the matrix"]
#guard red chain [{ site false 3 with rng := some 0 }, site true (3 + len + 2)] ==
  ["link 0, calls: at the digits alone a round is named that draws the matrix",
   "link 0, calls: that round is the link's, named RNG, draws matrix entries, and stands in front"]
-- a half of one part with all the rounds: the cut alone
#guard red chain sites lotName
    [⟨pl 0 2, [idlePart len]⟩, ⟨pl 0 7, idleRow (site true 0).at_⟩] ==
  ["link 0, calls: the half is cut as the book cuts"]
-- another lot's name; a name that two lots bear would fail alike
#guard red chain sites "K3" == ["just one lot of the description bears the name"]
-- the second site lacks
#guard red chain [site false 3] ==
  ["a site at every address of the lot's list", "as many sites as the chain has blocks of the kind",
   "no block of the kind that sends something lacks a half"]
-- a half more, at a place without a sub-protocol
#guard red chain sites lotName (halves sites ++ [⟨pl 0 9, []⟩]) ==
  ["a half for each site, in order", "no half without a block"]
-- two halves at one place
#guard red chain sites lotName (halves sites ++ halves [site true 0]) ==
  ["a half for each site, in order", "no two halves at one place"]
-- the place's name says another caller
#guard red chain [site false 3 "attention", site true (3 + len + 2)] ==
  ["link 0, calls: the caller is the one that the place's name says"]
-- a shape of one call (that the seated hearing rejects every run there is not shown in this file)
#guard red chain [{ site false 3 with shape := { NC := 1 } }, site true (3 + len + 2)] ==
  ["link 0, calls: the shape has several calls, as the seated hearing asks"]
-- nothing at all: no chain, no address, no site: the tests do not pass
#guard red [] [] lotName [] 0 == ["the lot's list has an address"]
-- a site at a place of another link than it says
#guard (failing (siteTests chain { site false 3 with link := 1 }
    (some (⟨pl 0 2, idleRow (site false 3).at_⟩ : Placed Unit Unit Unit)))) ==
  ["the place is chain 1, the site's link, the kind K3",
   "the caller is the one that the place's name says"]

-- the small face's numbers, written: 2 quiet rounds, 2 tie steps of 3 rounds, JOIN, the key tree's
-- levels of 0, 1, 2 variables (3 + 4 + 5 rounds and a LINE each), the table's level of 2 variables
-- (5 and a LINE), the leaves (1 + 3), ZERO, the bits (3 + 3)
#guard len == 2 + 6 + 1 + (3 + 4 + 5 + 3) + 6 + 4 + 1 + 6
#guard (idleRow (site false 3).at_ : List (Part Unit Unit Unit)).length == 2 + 2 + 1 + 6 + 2 + 3

-- seated by `Part.lift` a row keeps its parts and rounds
#guard ((seatRow (fun (_ : Nat) => ()) (idleRow (site false 3).at_) :
    List (Part Nat Nat Nat)).map (·.moves.length)) ==
  (stages face).map (Stage.rounds face)

end LotToy

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.lotName_is
