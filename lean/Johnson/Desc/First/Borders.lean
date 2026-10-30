-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Borders.lean: the table of joints of a proof file's first chain: what the state
that each block hands to the next means. Definitions with code. No theorem is proved in this file.
It imports Johnson/Desc/First/Driver/Chain.lean, State.lean and Johnson/Desc/Msg.lean alone: no
Mathlib: so a compiled run can evaluate the index, the open sets and the tests on the table.

The form. A border lies in front of each block of the chain's flat list (`Chain.blocksInOrder`,
Johnson/Desc/Block.lean) and behind the last. The relation at a border is computed, not written: it
is "every open item holds". An item is a named claim on the witness. A block's row says which items
the block closes (`ins`), which it opens (`outs`), which it reads and leaves (`ctx`), and whether
its extractor lays anything. open (k + 1) := (open k less ins k) with outs k. So the relation behind
a block is the relation in front of the next, by construction; what only rides past a block is
whatever stays open. Of a kind one law is asked: from its ins (with ctx) to its outs (with ctx):
`Piece.Own` (Johnson/Desc/Sound/Spine.lean); the riding is a law by sort of item.

The promise's twin. A kind's law enters the table only if what it asks of the public record in
front of its block follows from the table's promise there. A promise runs forward: each block
delivers behind what the next asks in front. So the promise has rows too (`PubRow`): a public item
(`Pub`) is a named Bool on the record; a row says which it asks in front, which it makes, which it
drops; the open public set at a border is computed forward (`pubSets`); some are tied to open items
instead (`pubOfItems`: each is made by the block that opens its item: `tiedMakers`, `tiedFit`); the
promise asks every open one (`pubHeld`). A block's law must also give: what is open behind holds
behind. `pubFit`: whatever a row asks or drops is open in front of it.
The door (`Pub.more`, `More`): the list of public items is shut; a clause that a kind's law
finds lacking comes by a filling: a name that begins with its kind, its rows (names alone: a filling
can add clauses; it can neither strike nor move one of the table's), its Bool. On these terms:
`pubFit` over the merged rows says true at both real lists, with a control; the item's Bool has run
true at every border at which it is open, on an honest walk, before a law that spends it counts; at
the empty filling the table is this file's own. The named items are not constructors of `Pub`: they
stand under the one constructor `Pub.more`, by name.


1 the index: `flatPlaces`: the places of the flat list's blocks: the driver's own `flatPlacesOf`;
  `borderAt`: a border's number by the place of the block behind it; `placesFit`: a test that a
  chain's flat list has just these places. A block that joins two steps (a sending or a switch with
  a quiet step behind it; the reply's with the head's entering) is one block here: what holds
  between its two halves is its own law's matter, not a border's: no promise stands there.
2 the items: `Part`, `RowClass`, `Item`.
3 the rows: `BlockRow`, `rowOf`.
4 the open sets: `start`, `stepOpen`, `openSets`; tests on the table: `readsOpen`, `closesAll`,
  `laysClear`, `laysAll`, `notYet`.
5 the plan's numbers, as letters: `Numbers`, with a test against the description's own oracles
  (`numbersFit`); which components of the witness an item reads (`Item.reads`) and a block's
  extractor lays (`laysOf`).
6 the meaning: the witness is `Wit` (Johnson/Desc/Msg.lean); `Meaning`: what an item says: a record
  of named fields, left open in this file; `unmarked` alone is a definition here.
7 the promise: `shapeAt` (a Bool on the state), `onAt`.

Whose the rows are. The form and the rows of a feed-forward segment come
from two texts of this project that are not in this repository, "BORDERS" and "the spine":
they were written from the byte format's pages, and they are not
checked. Each row's field `whose` is a note in plain words on that row;
it is read by no theorem. The rows here differ from those texts in these
points:
(a) `Item.wo`: the claim on the weights that a
bearing segment's own rounds leave rides as an item of its own until the frame's block "cleared":
that block lays the pending row on the pile and leaves the segment; the closing's block ends in
front of it; (b) the forms of a lookup's runs "planes" and "join" are opened behind the caller's own
hearing, not behind the lookup: they read what the caller hears; at the lookup's own border stand
two sentences on the committed messages at the heard points (`Item.worth`), which the caller's block
exchanges for these forms; (c) the frame's block "behind the batching" lays the virtual rows'
weights and no row: it carries total from one state to the next; the one equation's row is laid by
the closing's first block, a block of K9 without a round; K10's block takes it; a third block, of K9
again, shuts the segment; (d) `Item.unmarked`: a deferred mark (`S.failed`) stands in the relation,
and a marked record is inside every promise; it stands in every block's row (a block that marks and
goes on says yes at every challenge); (e) outside the pad's places the witness has one component for
all copies of a kept message (`Reading.arr`, Johnson/Desc/Msg.lean): so the segments of a witness
fit each other by make, and no item says that a copy is its original. At the pad's places each copy
has a component of its own, numbered by its seat (`Wit.pad`; `Comp.pad`): a kept message is sent
again with another pad (OnBytes/Iop/Cs.lean's head: "Its table is the old one except at the pad"),
and a pin compares the whole message: with one component for all the old copy's pin and the new
copy's would ask one component to be two tables: no honest run would meet a switch's row. A pin
still compares every place, so no place is free. A copy's pad is laid, off that copy's own decoding,
by the block that closes its pin: its group's closing; for a kept copy the next switch, whose
extractor lays that and nothing else; (f) `Item.tie` and `Item.formsT`: the reads are true: the
forms that are heard in front of moment 1 name entries of the array that is committed at moment 1:
until then they are read as the stated function of the cells (`formsT`); that sending exchanges them
for the forms at the committed array and opens the tie; the smallness test closes it; (g) no item
for a fold's fresh mask: nobody spends it: see three masks; (h) no item for the reply: the witness
has a component for it; the block that hears it lays it; (i) a group's pins are closed by its
closing (K10: in the library the batching on a group hands the pins back), not by the next switch:
between two segments ride the carried claim and the kept members' pins alone.

How the first chain sees the committed weights. The stored table is an oracle of the
statement at every border of the chain, though no block of the chain opens a leaf of it; the witness
is one for the file; its cells are tied to that oracle by `pinW`, which stands in the ctx of every
block whose items read the weights, under the promise "the stored table decodes with the record";
the claim on the weights is an open item (`wo`, then `pile`) from the sumcheck that leaves it to the
shared chain. Which stored table where there are two: the key file's table's to say; failing that,
the one that the plan's own stored part names.

Of no kind is an extractor of its own asked. The table has one, made once (`extQ`,
Johnson/Desc/Sound/BordersFill.lean): the witness with the components that the row lays set to what
the statement's oracles decode to (at the reply's block: the token that the record behind has
heard); at a row that lays nothing it is the identity. A kind's law then reads: outside the round's
lost set, for every w: its outs at (b, w) give its ins at (a, extQ … w), and the promise behind is
kept. Why at one w and not "there is a w" inside each law: plain laws do not join beside a carried
claim on the same component (Johnson/Desc/Sound/SpinePlain.lean has the two-line model). A hidden
object that no sample pins (the code word named behind a closing's first round) is no component of
the witness: it stands under its own "there is" inside the item's meaning.

Three masks, and which of them is a component of the witness. (1) The segment's mask row:
entry j belongs to slot j: the hidden value under a slot is what was shown less a public factor
times that entry (OnBytes/Model/Hide.lean, at `Fork`): every form of K3, K4, K5, K6, K8 and K9 reads
it. It is a table of the segment's first oracle message, which has a sample: a component with a PIN:
it is among `pin m 0`, which stands in the ctx of all these rows. (2) The index masks' message:
sampled: `pinI`: it masks a merge's end value and the pending rows. (3) The fold's fresh mask: "It
gets no out-of-domain sample … is read only at the positions of the step that follows this FOLD …
One mask serves one fold" (OnBytes/Iop/Fold.lean): no component, and no item: the library's closing
with the mask sent earlier takes the mask's word as a further oracle that neither its relation nor
its condition in front reads (`kBatFoldRide`, Johnson/Top/H/BatFold.lean; `Rels.keepE`,
Ior/Frame.lean): any word that stands in the statement in front of the block; so do the proximity
tests' laws. That it was sent before the fold's first draw is a fact of the plan's order. An item
that no row spends asks a law for nothing.

What rides, by sort of item (the frame facts; each one law for the whole file): (1) constr: no block
writes the request; the extractor leaves the components read; (2) the pins: a tree that was
sent passes every later block unturned; the samples are held; (3) forms, formsT, worth: a later
block writes neither what this block heard nor its slots: the ledger only grows (other files'
"LedgerKeeps"; `RunsFill.later`); (4) total, row, carry, wo, pile: rows are only added; the
ledger is not touched outside its segment; (5) at a row that lays: no other open item reads what it
lays (`laysClear`); (6) of the record, by every block: a mark stays; (7) by every block but the
reply's: what the record holds of the reply is the same behind as in front (nobody else lays that
seat).

What is in no item, and what shows it. That the token which the reply's block's extractor lays is
the token that the file's last test compares: no item: asked beside the relations (other files'
two fields "reads" and "fins" of what is asked of a description; three small laws in yet other
files: the reply is laid once, left by every later block, and passed to the last test). The reply's
seat in the record is meant as `S.out.reply` (one seat, laid by the reply's own block alone):
that text is not the one that rides: in every fold that has ridden that seat is laid one block
later, by the switch behind the reply's block, and honest runs show it so: at these folds the
reply's row (what it opens; the token that it lays) cannot be met at a reader of that seat alone:
either the reader takes what the reply's block has heard from where that block lays it, or the row
is said of the other text. That the request in what was handed to the chain and the request in the
state are one: it has no payer.

Every block of the first chain has a row. The other two chains and the key file have theirs
in their own files; the entry file has none anywhere.

Limits. (1) No theorem checks the rows; a row's field `whose` is a note in plain words on that row;
every sort of item but `unmarked` has a letter for its meaning here. (2) What an honest
run can show of the promise: the book-keeping and that the samples are held: Bools on the record.
"No collision" and "the stored table decodes" are no Bools, and no program evaluates them at the
release's codes: they want an argument. (3) The tests on the table test the table's own word
(`Item.tenants` is by groups; `numbersFit`, which ties `Numbers` to the description's own oracles,
isn't run here: at empty lists every pin holds for nothing; at `arr := fun _ _ => 0` all tenants are
one component). The test that a count needs is not "every tenant that an item reads is pinned" (the
smallness test's forms read an array that is sent behind its draw, and soundly) but "the set of bad
challenges is a function of what is pinned": each kind's to show. (4) A pin may be read by several
tests: every test but the last has it as context; the last closes it. (5) The three chains have
three records: the items' meaning is wanted thrice; what is open at this chain's end (`unmarked`,
`pinW`, `pileOne`, `pinI`, `pinV`) is closed beyond it: by the second chain's start (a marked record
is refused there) and by the other chains' rows; at the file's end nothing that reads the witness
may be open. (6) A kind whose law is proved from a count of field values must give the pull-back
along the reading of a written round's challenge too.

What of `verify-on-bytes` is reached (marked here once): every row over
`S` reaches six constants of it, and the same six: `OnBytes.Model.LinkCtx`, `OnBytes.Statement`,
`OnBytes.TreeBook`, each with its constructor: three record types, no function: they come in with
State.lean's record itself. `rowsHeld` reads, through the statement's own
fields, `OnBytes.Group`, `OnBytes.Row` and `OnBytes.RowKind` too: two record types and a list of
three names, no function: by reading alone.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Driver.Chain
import Johnson.Desc.First.State
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-! ## 1 The index -/

/-- The places of the first chain's flat list: THE DRIVER's OWN LIST (`flatPlacesOf`,
Johnson/Desc/First/Driver/Chain.lean: the front · each segment: laid · the hearing blocks · the
batching · behind the batching · THE CLOSING's THREE BLOCKS · cleared · the blocks behind the last
segment · the seal): the table keeps no list of its own. front := false: without the chain's front
(for a control). -/
def flatPlaces (front : Bool) (links : List ModelPart) (several : Bool) : List Place :=
  if front then flatPlacesOf links several else (flatPlacesOf links several).drop 1

/-- The number of the border IN FRONT OF the block at a place (the border behind it has one more).
-/
def borderAt (ps : List Place) (p : Place) : Option Nat :=
  (ps.zipIdx.find? fun x => x.1 == p).map (·.2)

/-- A chain's flat list has just these places, in this order. -/
def placesFit {S Cl : Type} (c : Chain S Cl) (ps : List Place) : Bool :=
  c.blocksInOrder.map (·.place) == ps

/-! ## 2 The items -/

/-- The parts of a segment's relaxed relation. -/
inductive Part where
  /-- the identities vanish: all but the rider's, which is a part of its own -/
  | idn
  /-- every key of a call lies in its table -/
  | lookCalls
  /-- the caller's identity that borrows the lookup's point holds at every position (feed-forward:
  the selector's entries sum to 1; attention: the denominator is the sum of the softmax weights; the
  head: clip, table) -/
  | rider
  /-- SEGMENT m's COMMITTED SYMBOLS, AS THE WITNESS HOLDS THEM, ARE THE PACKING OF SMALL INTEGERS
  (the library's "Base"), and with it the model's clause "every cell is small". Where the map to the
  model's integers reads them by unpacking, the model's clause alone is true of every witness: it is
  the packing that the smallness test's law gives and that the rows in front of that test read (it
  stands in their ctx): under it the casts of these integers are the committed cells -/
  | small
  /-- every digit lies in the digits' table -/
  | lookDigits
  /-- the head's "every key of a call lies in its table", of the reply THAT THE RECORD HAS HEARD in
  the place of the witness's token (THE TOKEN STANDS IN THE KEYS, not in the identities: it enters
  the head's text through the winner alone: the top digit's key, the true sum of logits, the claim
  on the weights) -/
  | lookCallsHeard
  deriving DecidableEq, Repr

/-- The classes of rows on a segment's group. A ROW BEARS NO CLASS: of a row the statement tells
only whether it is plain, a sample's or a generator's; "carried" and "equation" are both plain. SO A
CLASS THAT LIES IN THE GROUP's LIST OF OPEN ROWS IS A RUN OF PLACES IN THAT LIST (`Group.rows`: in
the order of laying): its first place and its count are numbers of the plan (`Numbers.rowsAt`). A
row is pushed at the list's end, and nothing but the beginning of the group's test takes a row away
or moves one (BY `verify-on-bytes`'s TWO FUNCTIONS; for the description's blocks: OWED, on the
statement's side): so a class says ONE thing at every border at which it is open. THE PLACE IS NOT
THE NUMBER IN THE ORDER IN WHICH THE TEST TAKES THE ROWS: that order is: the plain rows, the
members' sample rows, the generators' rows: there the equation stands in front of the positions'
rows. -/
inductive RowClass where
  /-- the carried claim restated, and behind it the kept messages' EARLIER samples, restated as
  plain rows on the new copies: what the switch lays first -/
  | carried
  /-- the sample rows of the messages that are sent at this moment (0, 1, 2): ONE ITEM A MOMENT:
  opened by that moment's sending and never turned. (A sample row lies on its message: it is claimed
  from the admitting on, also while the message has joined no group yet.) -/
  | sample (moment : Nat)
  /-- the drawn positions' rows: what the switch lays behind these, in the same call -/
  | position
  /-- the segment's one equation: the list's last row -/
  | equation
  deriving DecidableEq, Repr

/-- The class lies in the group's list of open rows. (A sample row lies on its message.) -/
def RowClass.inList : RowClass → Bool
  | .sample _ => false
  | _ => true

/-- What the statement tells of a row of the class. -/
def RowClass.kind : RowClass → OnBytes.RowKind
  | .carried => .plain
  | .sample _ => .sample
  | .position => .generator
  | .equation => .plain

/-- **An item**: a named claim on the witness. seg: the segment's number, from 0. -/
inductive Item where
  /-- a part of the segment's relaxed relation holds of the witness's cells and weights -/
  | constr (seg : Nat) (part : Part)
  /-- the witness's messages of the sampled tenants that the segment sends at this moment (0, 1, 2)
  are what their committed words decode to with their samples -/
  | pin (seg moment : Nat)
  /-- the pins of those messages of the segment's group that the next segment keeps -/
  | pinKept (seg : Nat)
  /-- THE READS ARE TRUE: each entry of the array that the segment commits at moment 1, and that a
  form names, is the stated function of the cells -/
  | tie (seg : Nat)
  /-- the like of `pin` for the index masks' message -/
  | pinI
  /-- the like for the message W, which the chain's last sending commits -/
  | pinV
  /-- the witness's weights are what the stored table decodes to with the record -/
  | pinW
  /-- every form behind this run of the block at this piece has the value 0. THE FORMS ARE FREE OF
  THE BATCHING's DRAW and read what was HEARD, the slots' public kinds and the witness -/
  | forms (seg piece : Nat) (run : String)
  /-- the same forms, with each entry of the array that is committed LATER (at moment 1) read as the
  stated function of the cells, which are pinned: so that the forms' values are fixed before the
  draws
  -/
  | formsT (seg piece : Nat) (run : String)
  /-- the committed messages, AT THE POINTS THAT THE LOOKUP AT THIS PIECE HAS HEARD, are worth what
  lies under its slots ("planes": the planes' matrix at its two points; "keys": each call's key
  vector at its point; "rider": the caller's identity at the lookup's point, at true values, is 0):
  a sentence on the witness that can stand at the lookup's own border -/
  | worth (seg piece : Nat) (what : String)
  /-- what the own rounds leave for the row on the weights -/
  | wo (seg : Nat)
  /-- the forms' sum under the powers of the batching's draw is 0, READ AT THE STATE BEHIND THE RUNS
  BEHIND THE BATCHING (which lay the virtual rows' weights) -/
  | totalB (seg : Nat)
  /-- the same sentence, read at the border's own state -/
  | total (seg : Nat)
  /-- every row of this class holds: at a class in the group's list: the rows at the class's places
  (THAT THERE IS A ROW AT EACH PLACE IS THE PROMISE's: `rowsHeld`: the term that fills the letter is
  true of a place without a row); at a moment's samples: the sample rows of the messages that the
  segment sends at that moment -/
  | row (seg : Nat) (cls : RowClass)
  /-- the one claim that the closed segment hands on -/
  | carry (seg : Nat)
  /-- every pending row on the table of weights holds -/
  | pile
  /-- the one claim on the weights into which the pending rows are joined -/
  | pileOne
  /-- the rows on W hold -/
  | wrow
  /-- NO NAMED TEST ON VALUES HAS FAILED: a record that bears a mark has no witness. A deferred mark
  stands in the RELATION, never in the promise: a cheating prover makes a block mark and say yes at
  every challenge -/
  | unmarked
  deriving DecidableEq, Repr

/-! ## 3 The rows -/

/-- **A block's row.** -/
structure BlockRow where
  /-- the items that the block closes: they hold in front if … -/
  ins : List Item := []
  /-- … the items that it opens hold behind -/
  outs : List Item := []
  /-- the items that it reads and leaves open -/
  ctx : List Item := []
  /-- its extractor lays components of the witness (else it is the identity) -/
  lays : Bool := false
  /-- the row is filled; false: it is not -/
  known : Bool := true
  /-- a note in plain words: what the row's block is -/
  whose : String := "the frame's"
  deriving Repr

/-- What ties the witness to a segment's group: the three moments' pins. -/
def pinsOf (m : Nat) : List Item := [.pin m 0, .pin m 1, .pin m 2]

/-- By how much the head's segment's blocks are shifted: the reply's block stands in front. -/
def shift (sub : ModelPart) : Nat := if sub == .head then 1 else 0

/-- The piece whose block states the run "join": the lookup's; at the head the caller's. -/
def joinAt (sub : ModelPart) : Nat := if sub == .head then 4 else 2

/-- The runs of forms that are heard in front of moment 1: (piece, run). -/
def earlyRuns (sub : ModelPart) : List (Nat × String) :=
  let o := shift sub
  [(2 + o, "objects"), (2 + o, "planes"), (joinAt sub, "join"), (3 + o, "own")] ++
    (if sub == .head then [(3 + o, "weights")] else [])

/-- All that a segment's batching closes: the forms; and, of the lookup on the digits, the two
sentences at its heard points: NO HEARING BLOCK STANDS BETWEEN THAT LOOKUP AND THE BATCHING: the
exchange (the claims of the smallness test's own run of equations, judged behind the runs, are worth
these two) is the batching's front's. -/
def formsOf (sub : ModelPart) (m : Nat) : List Item :=
  let o := shift sub
  [.forms m (2 + o) "objects", .forms m (2 + o) "planes", .forms m (joinAt sub) "join",
   .forms m (3 + o) "own", .forms m (5 + o) "small", .forms m (7 + o) "objects",
   .worth m (7 + o) "planes", .worth m (7 + o) "keys"] ++
    (if sub == .head then [.forms m 9 "merged"] else [])

/-- **THE DRIVER's OWN NAMES OF THE RUNS THAT AN ITEM `forms | formsT m k r` STANDS FOR**: a block
in front of the batching, counted from 0 in the order of `kindsBeforeBatching`, and one of its lists of claims
(Johnson/Desc/First/Driver/Chain.lean, the protocol's order of a segment's claims). A run's reader
is looked up by THESE pairs; the table's names are its own. WHERE THE TWO PART: k is the block's
number + 1, but at "join" (layers, attention: the caller states it; the table's name bears the
lookup's piece) · "own" stands for all the caller's own runs · at a layers' segment the driver has
no run "planes" or "join": these claims lie inside the caller's "front" and "back": THE TWO ITEMS
ARE IDLE THERE · "small" stands for the smallness test's one run; of its claims those that bear no
number of an equation are what `worth m (7 + o)` says · "weights" at the head is a claim that no run
states. -/
def runsOf (sub : ModelPart) (k : Nat) (r : String) : List (Nat × String) :=
  let o := shift sub
  if k == 2 + o && r == "objects" then [(1 + o, "objects"), (1 + o, "guests")]
  else if k == 7 + o && r == "objects" then [(6 + o, "objects"), (6 + o, "guests")]
  else if k == 5 + o && r == "small" then [(4 + o, "K8.equations")]
  else if k == 2 + o && r == "planes" then (if sub == .layers then [] else [(1 + o, "planes")])
  else if k == joinAt sub && r == "join" then (if sub == .layers then [] else [(2 + o, "join")])
  else if k == 3 + o && r == "own" then
    match sub with
    | .layers => [(2, "front"), (2, "back")]
    | .attention => [(2, "first"), (2, "keys"), (2, "second")]
    | .head => [(3, "norm"), (3, "policy"), (3, "logits")]
  else if sub == .head && k == 9 && r == "merged" then [(8, "the merge")]
  else []

/-- The runs that the table names at a sort of segment. -/
def tableRuns (sub : ModelPart) : List (Nat × String) :=
  ((formsOf sub 0).filterMap fun i => match i with
    | .forms _ k r => some (k, r)
    | _ => none) ++ (if sub == .head then [(4, "weights")] else [])

/-- A TEST ON THE TABLE, against a list of the driver's pairs (its order of a segment's claims):
every pair of that list falls under just one name of the table, and the table names no other. -/
def runsFitBy (order : List (Nat × String)) (sub : ModelPart) : Bool :=
  let l := (tableRuns sub).flatMap fun x => runsOf sub x.1 x.2
  l.all order.contains && order.all l.contains && l.eraseDups.length == l.length

/-- The rows on a segment's group in front of the closing's second block (K10's): the one equation's
among them: the closing's first block has laid it. -/
def rowsOf (m : Nat) : List Item :=
  (if m == 0 then [] else [.row m .carried, .row m .position]) ++
    [.row m (.sample 0), .row m (.sample 1), .row m (.sample 2), .row m .equation]

/-- **The rows of a segment**, by the block's number in the segment. The rows that the head names,
with the verdict on them and the changes named in this file's head; unchecked. A feed-forward
segment bears a claim on the weights (`wo`) from its own rounds; an attention segment bears none;
the head's segment has the reply's block in front (K7: ITS EXTRACTOR LAYS THE WITNESS's TOKEN: in
front of it the head's keys speak of the witness's token, behind it of the reply that the record has
heard) and the merge (K11) as a block of its own. -/
def segRow (sub : ModelPart) (m piece : Nat) : BlockRow :=
  let o := shift sub
  if piece == 0 then {}
  else if sub == .head && piece == 1 then
    { ins := [.constr m .lookCalls], outs := [.constr m .lookCallsHeard], lays := true
      whose := "the reply's block (K7): the token stands in the keys" }
  else if piece == 1 + o then
    if m == 0 then
      { outs := [.pin 0 0, .pinI, .row 0 (.sample 0)]
        whose := "a sending (K1)" }
    else
      { ins := [.carry (m - 1), .pinKept (m - 1)]
        outs := [.pin m 0, .row m .carried, .row m (.sample 0), .row m .position], lays := true
        whose := "a code switch (K2); lays: " ++
          "the old copies' pads" }
  else if piece == 2 + o then
    { ins := [.constr m (if sub == .head then .lookCallsHeard else .lookCalls), .constr m .rider]
      outs := [.formsT m (2 + o) "objects", .worth m (2 + o) "planes", .worth m (2 + o) "keys",
        .worth m (2 + o) "rider"]
      ctx := .pin m 0 :: .constr m .small :: (if sub == .attention then [] else [.pinW])
      whose := "the lookup on the calls (K3)" ++
        "; small stands in ctx" }
  else if piece == 3 + o then
    { ins := [.constr m .idn, .worth m (2 + o) "planes", .worth m (2 + o) "keys",
        .worth m (2 + o) "rider"]
      outs :=
        [.formsT m (3 + o) "own", .formsT m (2 + o) "planes", .formsT m (joinAt sub) "join"] ++
        (if sub == .layers then [.wo m] else []) ++
        (if sub == .head then [.formsT m (3 + o) "weights"] else [])
      ctx := [.pin m 0, .pinW, .constr m .small] ++ (if sub == .layers then [.pinI] else [])
      whose := "small stands in ctx; " ++ match sub with
        | .layers => "the layers' own rounds (K4)"
        | .attention => "the attention's own rounds (K5); pinW in ctx: in doubt"
        | .head => "the head's own rounds (K6): idn; join is its own run" }
  else if piece == 4 + o then
    { ins := (earlyRuns sub).map fun x => .formsT m x.1 x.2
      outs := .pin m 1 :: .row m (.sample 1) :: .tie m ::
        (earlyRuns sub).map fun x => .forms m x.1 x.2
      ctx := [.pin m 0, .constr m .small]
      whose := "a sending (K1) with the tie (K8): " ++
        "forms and the tie give formsT" }
  else if piece == 5 + o then
    { ins := [.constr m .small, .tie m], outs := [.forms m (5 + o) "small", .constr m .lookDigits]
      ctx := [.pin m 0, .pin m 1]
      whose := "the smallness test (K8); " ++
        "small says the packing too: its law owes that" }
  else if piece == 6 + o then
    { outs := [.pin m 2, .row m (.sample 2)]
      whose := "a sending (K1)" }
  else if piece == 7 + o then
    { ins := [.constr m .lookDigits]
      outs := [.forms m (7 + o) "objects", .worth m (7 + o) "planes", .worth m (7 + o) "keys"]
      ctx := [.pin m 2, .pin m 0, .pin m 1]
      whose := "the lookup on the digits (K3): ctx as in its lemma" }
  else if sub == .head && piece == 9 then
    { ins := [.forms m 4 "weights"], outs := [.forms m 9 "merged", .wo m]
      ctx := [.pinW, .pin m 0, .pinI]
      whose := "the merge (K11); pin m 0 stands in ctx" }
  else if piece == 8 + 2 * o then
    { ins := formsOf sub m, outs := [.totalB m], ctx := pinsOf m
      whose := "the batching (K9), with the digits' exchange" }
  else if piece == 9 + 2 * o then
    { ins := [.totalB m], outs := [.total m], ctx := pinsOf m
      whose := "the runs behind the batching (laid by Block.lean, `Link.flat`): they lay no row" }
  else if piece == 10 + 2 * o then
    { ins := [.total m], outs := [.row m .equation]
      whose := "the closing's first block (K9, no round): the one equation: total to the " ++
        "equation's row" }
  else if piece == 11 + 2 * o then
    { ins := rowsOf m ++ pinsOf m, outs := [.carry m, .pinKept m], lays := true
      whose := "the closing's second block (K10): the shape of its law, " ++
        "with five bounds" }
  else if piece == 12 + 2 * o then
    { whose := "the closing's third block (K9, no round): the segment is shut: it writes the " ++
        "segment's book-keeping alone: no item" }
  else if piece == 13 + 2 * o then
    if sub == .attention then {}
    else
      { ins := [.wo m], ctx := [.pile, .pinW, .pinI]
        whose := "the segment's frame's: it lays the pending row" }
  else { known := false }

/-- **The rows behind the last segment**, by the block's kind. n: the number of segments; the last
switch's group has the number n. K13's row: Lean takes its law there in its own
form (one relation at both borders: the stored table's and the index masks' pins, and every row of
`S.rows` holds): here: `pile`, `pinW` and `pinI` as context. THE CLAIM ON THE WEIGHTS STAYS OPEN
THROUGH W's SENDING: that W is the combination of the matrix's rows is said by nothing in front of
the shared chain's point: the rows on W (`wrow`) are opened there, not here. -/
def backRow (n : Nat) (p : Place) : BlockRow :=
  match p.kind with
  | .K2 =>
    { ins := [.carry (n - 1), .pinKept (n - 1)]
      outs := [.pin n 0, .row n .carried, .row n (.sample 0), .row n .position], lays := true
      whose := "a code switch (K2); lays: " ++
        "the old copies' pads" }
  | .K12 =>
    { ins := [.row n .carried, .row n (.sample 0), .row n .position, .pin n 0], lays := true
      whose := "the last proximity test (K12): no near n: no row spends it" }
  | .K13 =>
    { ins := [.pile], outs := [.pileOne], ctx := [.pinW, .pinI]
      whose := "the joining of the pending claims (K13): the block turns what pile reads" }
  | .K1 =>
    { outs := [.pinV], ctx := [if p.piece == 4 then .pileOne else .pile, .pinW]
      whose := "a sending (K1)" }
  | _ => {}

/-- **The table**: the row of the block at a place. links: the segments' sorts. -/
def rowOf (links : List ModelPart) (p : Place) : BlockRow :=
  match p.link with
  | some m =>
    match links[m]? with
    | some sub => segRow sub m p.piece
    | none => { known := false, whose := "NO SUCH SEGMENT" }
  | none => if p.piece == 0 then {} else backRow links.length p

/-! ## 4 The open sets -/

/-- What is open at the chain's start: no mark; the stored table's pin; the (empty) pile; each
segment's relaxed relation in its parts. -/
def start (links : List ModelPart) : List Item :=
  [.unmarked, .pinW, .pile] ++ links.zipIdx.flatMap fun x =>
    [.constr x.2 .idn, .constr x.2 .lookCalls, .constr x.2 .rider, .constr x.2 .small]

/-- The open set behind a block. An item of `ctx` stays; an item that is opened twice stands once.
-/
def stepOpen (O : List Item) (r : BlockRow) : List Item :=
  let rest := O.filter fun i => !r.ins.contains i
  rest ++ r.outs.filter fun i => !rest.contains i

/-- The open sets at all borders: one more than there are blocks. -/
def openSets (links : List ModelPart) : List Place → List Item → List (List Item)
  | [], O => [O]
  | p :: ps, O => O :: openSets links ps (stepOpen O (rowOf links p))

/-- A TEST ON THE TABLE: every item that a block closes or reads is open in front of it. -/
def readsOpen (links : List ModelPart) : List Place → List Item → Bool
  | [], _ => true
  | p :: ps, O =>
    ((rowOf links p).ins ++ (rowOf links p).ctx).all O.contains &&
      readsOpen links ps (stepOpen O (rowOf links p))

/-- The segment whose part of the record an item's meaning reads; none: it reads no segment's part.
(`row` and `carry` have none: they read the statement's groups, which outlive their segment.) -/
def Item.part : Item → Option Nat
  | .forms m _ _ => some m
  | .formsT m _ _ => some m
  | .worth m _ _ => some m
  | .wo m => some m
  | .tie m => some m
  | .totalB m => some m
  | .total m => some m
  | _ => none

/-- A TEST ON THE TABLE: every part of every segment's relation that is open at the start is closed
by some row: else it stays open to the chain's end, where nothing can close it. -/
def closesAll (links : List ModelPart) (ps : List Place) : Bool :=
  (start links).all fun i => match i with
    | .constr _ _ => ps.any fun p => (rowOf links p).ins.contains i
    | _ => true

/-- How many blocks have no row. -/
def notYet (links : List ModelPart) (ps : List Place) : Nat :=
  (ps.filter fun p => !(rowOf links p).known).length

/-! ## 4b The public items: the promise's twin of the items -/

/-- **A PUBLIC ITEM**: a named condition ON THE PUBLIC RECORD ALONE (no oracle, no witness), which a
kind's law asks in front of its block. A PROMISE RUNS FORWARD: what is asked in front of a block
must be MADE by a named block in front of it and KEPT by every block between: so a public item has a
maker, riders and askers, as an item has an opener, riders and a closer; but its law runs the other
way: from the border in front to the border behind. THREE TERMS FOR A CLAUSE TO COUNT AS PAID (a
rule of this table): it is a Bool on the record · it has run true at every border at which it
is open, at both sizes, with a control · its maker is shown to make it and every kind that it
rides past to keep it. OF THE CONSTRUCTORS BENEATH NONE MEETS ALL THREE.
What hangs on the plan alone is no public item: it stands beside the tests on the plan. -/
inductive Pub where
  /-- the segment's ledger is well laid: its arrays have as many entries as it has slots -/
  | ledger (seg : Nat)
  /-- the request in the record passes the start's test. OPEN AT NO BORDER: no row asks, makes or
  drops it, and the start does not lay it open: no kind's law takes it from the promise (K6's block
  tests the request itself) -/
  | request
  /-- no reply has been heard yet, wherever the record would hold one: from the chain's start to the
  front of the reply's block -/
  | unheard
  /-- A TOKEN IS HEARD, and it is below the vocabulary's size (its maker's law proves both; the
  lookup on the calls at the head spends the first) -/
  | tokenSmall
  /-- where the segment's lookup on the calls is heard: every slot that its last claim names is
  filled in the ledger; AND, AT A LAYERS' OR AN ATTENTION SEGMENT, both readers of what it returned
  give one thing. (NOT AT THE HEAD: there the second reader answers nothing until the caller's own
  hearing: an honest record's two readers part in front of the caller's block.) -/
  | look (seg : Nat)
  /-- the caller's law's own condition in front of its block (K4 | K5 | K6): it has not been heard
  before in this segment; the ledger's next free slot is the plan's. (THE ROOM is `freeAbove`'s.) -/
  | callerIn (seg : Nat)
  /-- the lookup's law's condition in front of its block at this piece -/
  | lookIn (seg piece : Nat)
  /-- EVERY SLOT FROM THE LEDGER's NEXT FREE NUMBER ON IS FREE: made where the ledger is laid, kept
  by every hearing that fills just what it takes, up to the batching. NO BLOCK MAKES ROOM: each
  hands it on. Its test (`freeAboveB`, Johnson/Desc/First/FillKeeper.lean) also asks that the
  ledger's number of slots is the plan's: the free slots alone say WHICH are free, not how many
  there are: with that number, and a test on the plan, follow the room that a caller's script, the
  lookup on the digits and "the hearing returns" want -/
  | freeAbove (seg : Nat)
  /-- from the segment's opening to the lookup on the digits: nothing is heard yet at the digits'
  seat, and the open segment's table of arrays is the plan's: two conjuncts of `lookIn` at the
  digits that the caller's block, which makes that item, neither makes nor touches -/
  | linkFresh (seg : Nat)
  /-- WHAT THE LOOKUP ON THE CALLS LEFT: what was heard IS the end values of a hearing of SOME
  rounds from SOME ledger in front, and the ledger in hand is the one behind that hearing. NO Bool:
  the rounds are not in the record: it is said by `Meaning.pubP`. SPAN ONE: made by the lookup's
  block, asked and dropped by the caller's: no kind is asked to keep it -/
  | left (seg : Nat)
  /-- THE SAME IN THE FORM THAT STANDS AT EVERY LATER RECORD: "... and the ledger in hand is LATER
  than the one behind that hearing". Said by `Meaning.pubP` too. Made by the caller's block out of
  `left`; asked and dropped by the batching, whose runs' laws spend it at the snapshot. NOT OF SPAN
  ONE: kinds between must give "my yes leaves a later ledger and turns nothing of what was heard";
  the general half (kept by whatever does so) is not shown here -/
  | leftOn (seg : Nat)
  /-- at the chain's start: no oracle message has been sent yet: so that the first sending's
  messages have the numbers that the plan gives them -/
  | noneSent
  /-- the record's number of the index masks' message is the plan's (`Numbers.indexNo`). TIED TO
  `pinI`: the rows on the table name their mask entries BY THAT NUMBER, the pin speaks of the TENANT
  `Numbers.index`: without it the pin fixes nothing that these rows read -/
  | indexIs
  /-- and the statement holds a message of that number (tied to `pinI`) -/
  | indexThere
  /-- **THE DOOR**: a public item that comes BY A FILLING (`More`), not by a turn of this file: seg:
  its segment, if it is one segment's; name: BEGINS WITH ITS KIND ("K5.readsThere", "K10.on"): A
  RULE ON NAMES, HELD BY NO CODE: two fillings with one name ring only if both make it.
  What it says: `Meaning.pub` (and `pubP`) at it, as for every item. THE LIST OF CONSTRUCTORS IS
  SHUT: a new clause of the promise comes through here -/
  | more (seg : Option Nat) (name : String)
  /-- and behind it, up to the batching -/
  | lookOut (seg piece : Nat)
  /-- every form that the run's reader gives at the record names only what is there (TIED TO THE
  OPEN ITEM: asked wherever `forms` of that run is open) -/
  | formsIn (seg piece : Nat) (run : String)
  /-- the weaker like, wherever `formsT` of that run is open: ... or a cell of an array that the
  segment's next sending will bring. (ONE NAME FOR BOTH WOULD NOT DO: a public item's meaning sees
  the record and no border: at the stronger test the promise would be false at an honest record in
  front of that sending, at the weaker the closers of `forms` would get too little.) -/
  | formsInT (seg piece : Nat) (run : String)
  /-- the like for the batched form (tied to `total`) -/
  | totalIn (seg : Nat)
  /-- the record holds what the segment's pending row is made of (TIED TO `wo`: where it held
  nothing, "the row that will be laid holds of the witness" would be true of every witness) -/
  | hasRow (seg : Nat)
  /-- behind the joining of the pending rows: that block's law's condition -/
  | frontOk
  /-- behind W's sending: the like -/
  | evalLaid
  deriving DecidableEq, Repr

/-- **A block's row in the promise's table.** -/
structure PubRow where
  /-- what its kind's law asks of the record in front: it must be open there. (READ BY `pubFit`
  ALONE: the promise asks every open item, asked by the next block or not.) -/
  asks : List Pub := []
  /-- what holds of the record behind by the block's own doing -/
  makes : List Pub := []
  /-- what nobody behind the block asks any more -/
  drops : List Pub := []
  /-- a note in plain words: where the row's entries come from -/
  whose : String := ""
  deriving Repr

/-- The name of a public item that comes by a filling. -/
abbrev MoreName := Option Nat × String

/-- The item of that name. -/
def moreItem (x : MoreName) : Pub := .more x.1 x.2

/-- What a filling adds to a block's row: NAMES ALONE: it can add clauses; it can neither strike nor
move one of the table's own. -/
structure MoreRow where
  asks : List MoreName := []
  makes : List MoreName := []
  drops : List MoreName := []
  deriving Repr

/-- **THE DOOR's FILLING**: who asks, makes and drops the named items, place by place, and which are
open at the chain's start. EMPTY BY DEFAULT: then the promise's table is this file's own.
The named items are not constructors of `Pub`:
they stand under the one constructor `Pub.more`, each
by its name. -/
structure More where
  rows : List ModelPart → Place → MoreRow := fun _ _ => {}
  start : List MoreName := []

/-- Two fillings together: rows appended, place by place. -/
def More.merge (a b : More) : More where
  rows l p :=
    { asks := (a.rows l p).asks ++ (b.rows l p).asks
      makes := (a.rows l p).makes ++ (b.rows l p).makes
      drops := (a.rows l p).drops ++ (b.rows l p).drops }
  start := a.start ++ b.start

/-- A row of the table with what a filling adds. -/
def PubRow.plus (r : PubRow) (m : MoreRow) : PubRow :=
  { r with
    asks := r.asks ++ m.asks.map moreItem
    makes := r.makes ++ m.makes.map moreItem
    drops := r.drops ++ m.drops.map moreItem }

/-- The open public set behind a block. -/
def pubStep (Q : List Pub) (r : PubRow) : List Pub :=
  let rest := Q.filter fun q => !r.drops.contains q
  rest ++ r.makes.filter fun q => !rest.contains q

/-- The open public sets at all borders, at any rows: one more than there are blocks. -/
def pubSetsBy (rows : Place → PubRow) : List Place → List Pub → List (List Pub)
  | [], Q => [Q]
  | p :: ps, Q => Q :: pubSetsBy rows ps (pubStep Q (rows p))

/-- A TEST ON THE PROMISE's TABLE: whatever a block's law asks is open in front of the block;
whatever a row drops is open there; whatever it makes is not (or is dropped by the same row), and
stands once in the row's list. A TEST OF WELL-FORMEDNESS: IT IS TRUE OF THE TABLE WHOSE ROWS ARE ALL
EMPTY: it cannot see that a row asks too little, nor that an item is never dropped. -/
def pubFitBy (rows : Place → PubRow) : List Place → List Pub → Bool
  | [], _ => true
  | p :: ps, Q =>
    (rows p).asks.all Q.contains && (rows p).drops.all Q.contains &&
      ((rows p).makes.all fun q => !Q.contains q || (rows p).drops.contains q) &&
      (rows p).makes.eraseDups.length == (rows p).makes.length &&
      pubFitBy rows ps (pubStep Q (rows p))

/-- What is open at the chain's start: no reply has been heard; no oracle message has been sent. -/
def pubStart : List Pub := [.unheard, .noneSent]

/-- **THE PROMISE's TABLE**: the row of the block at a place. WHO MAKES WHAT IS SHOWN BY
NO THEOREM OF THIS FILE: the field `whose` of each row says where its entries
come from; at some rows it says of `callerIn`: "A GUESS". -/
def pubRowOf (links : List ModelPart) (p : Place) : PubRow :=
  match p.link with
  | some m =>
    match links[m]? with
    | none => {}
    | some sub =>
      let o := shift sub
      if sub == .head && p.piece == 1 then
        { asks := [.unheard], drops := [.unheard], makes := [.tokenSmall]
          whose := "unheard: asked for the law that the reply is laid once; " ++
            "K7's own text tests it; made by the start (proved: a first record holds no reply); " ++
            "tokenSmall: MADE HERE, in one step (the reply is laid by " ++
            "this block: by a run)" }
      else if p.piece == 1 + o then
        { asks := if m == 0 then [.noneSent] else []
          drops := if m == 0 then [.noneSent] else []
          makes := [.ledger m, .lookIn m (2 + o), .linkFresh m, .freeAbove m]
          whose := "the ledger, lookIn: BY A RUN (small; not over this State.lean): " ++
            "true from behind this block on" }
      else if p.piece == 2 + o then
        { asks := [.ledger m, .lookIn m (2 + o), .freeAbove m], drops := [.lookIn m (2 + o)]
          makes := [.lookOut m (2 + o), .look m, .left m] ++
            (if sub == .head then [] else [.callerIn m])
          whose := "lookIn, lookOut: the lookups' two Bools (run); look: by a reading; " ++
            "callerIn: A GUESS that it holds from behind this block on; NOT AT THE HEAD: no " ++
            "clause of K6's condition spends it" }
      else if p.piece == 3 + o then
        { asks := [.ledger m, .look m, .left m, .linkFresh m, .freeAbove m] ++
            (if sub == .head then [.tokenSmall] else [.callerIn m])
          drops := [.look m, .left m] ++
            (if sub == .head then [.tokenSmall] else [.callerIn m])
          makes := [.lookIn m (7 + o), .leftOn m]
          whose := (if sub == .head then "asks: K6's Bools"
            else "asks: after the head's; callerIn: at attention by a reading of K5's " ++
              "files; at layers A GUESS") ++
            "; makes: BY THE SAME RUN: the digits' lookIn is true from behind this block on" }
      else if p.piece == 7 + o then
        { asks := [.ledger m, .lookIn m (7 + o), .linkFresh m, .freeAbove m]
          drops := [.lookIn m (7 + o), .linkFresh m]
          makes := [.lookOut m (7 + o)], whose := "the lookups' two Bools (run)" }
      else if p.piece == 8 + 2 * o then
        { asks := [.ledger m, .lookOut m (2 + o), .lookOut m (7 + o), .leftOn m]
          drops := [.lookOut m (2 + o), .lookOut m (7 + o), .freeAbove m, .leftOn m]
          whose := "up to the batching's front: as the lookups' Bools have run" }
      else if p.piece == 10 + 2 * o then
        { asks := [.ledger m], drops := [.ledger m]
          whose := "the one equation's block tests the ledger (by a reading of its text); " ++
            "no row behind it asks for it" }
      else {}
  | none =>
    match p.kind with
    | .K13 => { makes := [.frontOk], whose := "made by this block; its Bool is not filled here" }
    | .K1 => { makes := [.evalLaid], whose := "made by this block; its Bool is not filled here" }
    | _ => {}

/-- The table's row with a filling's. -/
def pubRowM (M : More) (links : List ModelPart) (p : Place) : PubRow :=
  (pubRowOf links p).plus (M.rows links p)

/-- What is open at the chain's start, with a filling's. -/
def pubStartM (M : More) : List Pub := pubStart ++ M.start.map moreItem

/-- The open public sets at all borders, at a filling of the door. -/
def pubSets (M : More) (links : List ModelPart) (ps : List Place) : List (List Pub) :=
  pubSetsBy (pubRowM M links) ps (pubStartM M)

/-- A TEST ON THE PROMISE's TABLE, at a filling of the door: a misspelt name rings as "asked, and
made by nobody". ASKED OF EVERY FILLING: THAT THIS TEST SAYS TRUE AT THE REAL LISTS OF PLACES. -/
def pubFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  pubFitBy (pubRowM M links) ps (pubStartM M)

/-- The public items that are tied to open items. A TIED ITEM's MAKER IS THE BLOCK THAT OPENS THE
ITEM (`pubRowOf` names none): it is asked from the border behind that block on, as long as the item
is open; every block that the item rides past keeps it. -/
def pubOfItems (O : List Item) : List Pub :=
  O.flatMap fun i => match i with
    | .forms m k r => [.formsIn m k r]
    | .formsT m k r => [.formsInT m k r]
    | .total m => [.totalIn m]
    | .wo m => [.hasRow m]
    | .pinI => [.indexIs, .indexThere]
    | _ => []

/-- The tied public items that come at a block: tied to the items that its row opens. THEY ARE THAT
BLOCK's TO MAKE, beside its row's `makes`. -/
def tiedNew (r : BlockRow) (O : List Item) : List Pub :=
  (pubOfItems (stepOpen O r)).filter fun q => !(pubOfItems O).contains q

/-- **WHO MAKES THE TIED ITEMS**: each with the place of the block at which it comes. -/
def tiedMakersBy (rows : Place → BlockRow) : List Place → List Item → List (Pub × Place)
  | [], _ => []
  | p :: ps, O => (tiedNew (rows p) O).map (·, p) ++ tiedMakersBy rows ps (stepOpen O (rows p))

/-- At the table's own rows. -/
def tiedMakers (links : List ModelPart) (ps : List Place) : List (Pub × Place) :=
  tiedMakersBy (rowOf links) ps (start links)

/-- A TEST ON THE TABLE: EVERY TIED PUBLIC ITEM HAS ONE MAKER: none is open at the chain's start
(there it would have none); none comes twice (at two blocks); none stands among the rows' own items
(`makes`), where it would have two books. `pubFit` does not see the tied items: this test does. -/
def tiedFitBy (rows : Place → BlockRow) (pubs : Place → PubRow) (ps : List Place)
    (O : List Item) : Bool :=
  (pubOfItems O).isEmpty &&
    ((tiedMakersBy rows ps O).map (·.1)).eraseDups.length == (tiedMakersBy rows ps O).length &&
    (tiedMakersBy rows ps O).all fun x => ps.all fun p => !(pubs p).makes.contains x.1

/-- At the table's own rows. -/
def tiedFit (links : List ModelPart) (ps : List Place) : Bool :=
  tiedFitBy (rowOf links) (pubRowOf links) ps (start links)

/-! ## 5 The plan's numbers, as letters -/

/-- **What the table reads of the plan.** A tenant: a tree's number through the file, and the
message's number in the tree. -/
structure Numbers where
  /-- the sampled tenants that segment m sends at its moment t -/
  sent : Nat → Nat → List (Nat × Nat)
  /-- those tenants of segment m's group that the next segment keeps -/
  keptOf : Nat → List (Nat × Nat)
  /-- the tenant of the index masks' message -/
  index : Nat × Nat
  /-- that message's number among the statement's oracle messages. (That this message sits at the
  tenant `index` is a test on the plan that `numbersFit` does not make.) -/
  indexNo : Nat := 0
  /-- how many trees the blocks in front of the block at a place have sent (none: at the chain's
  end): so that a sending's new messages sit at the tenants that the plan gives them. THE DEFAULT,
  0 EVERYWHERE, IS FALSE OF AN HONEST RECORD BEHIND THE FIRST SENDING: it shows -/
  treesAt : Option Place → Nat := fun _ => 0
  /-- and how many oracle messages (the tenants of these trees). The default is false likewise -/
  msgsAt : Option Place → Nat := fun _ => 0
  /-- the tenant of the message W -/
  w : Nat × Nat
  /-- THE TENANTS THAT NO ITEM READS: those that ONE block both sends and tests (the last proximity
  test's later stages: a sampled target and a mask without a sample at each); and the first fold's
  mask of a closing or of a proximity test (every segment's; the last switch's; the one in W's
  tree): the law takes it as ANY
  word that is fixed before the fold's first draw: its nearness is given by nothing and spent by
  nothing (AN ITEM THAT NO ROW SPENDS ASKS A LAW FOR NOTHING) -/
  inside : List (Nat × Nat) := []
  /-- the number, in the statement, of segment m's group (the last switch's: m = the number of
  segments) -/
  groupAt : Nat → Nat := id
  /-- WHERE A CLASS LIES IN ITS GROUP's LIST OF OPEN ROWS: the first place, and how many rows. THE
  LAYING KIND's WORD, off the plan: the switch's for "carried" and "position", the one equation's
  for "equation" (laid by the closing's first block, taken by its second). Not read at a moment's
  samples -/
  rowsAt : Nat → RowClass → Nat × Nat := fun _ _ => (0, 0)

/-- The sampled tenants of a segment's group. -/
def Numbers.group (N : Numbers) (m : Nat) : List (Nat × Nat) :=
  N.sent m 0 ++ N.sent m 1 ++ N.sent m 2

/-- The tenants of a list of oracles that have a sample (or have none): (tree, tenant). -/
def tenantsOf (os : List Oracle) (sampled : Bool) : List (Nat × Nat) :=
  os.zipIdx.flatMap fun o =>
    (o.1.tenants.zipIdx.filter fun t => t.1.sampled == sampled).map fun t => (o.2, t.2)

/-- Two lists have the same members. -/
def sameMembers (a b : List (Nat × Nat)) : Bool := a.all b.contains && b.all a.contains

/-- No member stands twice. -/
def eachOnce : List (Nat × Nat) → Bool
  | [] => true
  | x :: l => !l.contains x && eachOnce l

/-- A TEST THAT TIES THE NUMBERS TO THE DESCRIPTION's OWN ORACLES. os: what the first chain's blocks
tell of the trees that they send (`oraclesOf F.first.blocksInOrder`). n: the number of segments. The sampled
tenants, but those of `inside`, are just those of `sent` (the last switch's group has the number n),
`index` and `w`; every tenant without a sample stands in `inside`; all these lists together name
each tenant once; what is kept lies in its group. -/
def numbersFit (os : List Oracle) (N : Numbers) (n : Nat) : Bool :=
  let smp := ((List.range (n + 1)).flatMap fun m => N.sent m 0 ++ N.sent m 1 ++ N.sent m 2) ++
    [N.index, N.w]
  sameMembers ((tenantsOf os true).filter fun x => !N.inside.contains x) smp &&
    (tenantsOf os false).all N.inside.contains &&
    N.inside.all (tenantsOf os true ++ tenantsOf os false).contains &&
    eachOnce (smp ++ N.inside) &&
    (List.range n).all fun m => (N.keptOf m).all (N.group m).contains

/-- The places of a class in its group's list. -/
def Numbers.places (N : Numbers) (m : Nat) (c : RowClass) : List Nat :=
  (List.range (N.rowsAt m c).2).map (· + (N.rowsAt m c).1)

/-- A TEST ON THE PLAN's NUMBERS: in each group's list the classes lie one behind the other, in the
order of laying: "carried" from place 0, "position" behind it, the one equation behind both; the
first segment's group has the equation alone, the last switch's has none; no two segments have one
group. n: the number of segments. -/
def rowsAtFit (N : Numbers) (n : Nat) : Bool :=
  eachOnce ((List.range (n + 1)).map fun m => (N.groupAt m, 0)) &&
    (List.range (n + 1)).all fun m =>
      (N.rowsAt m .carried).1 == 0 &&
        (N.rowsAt m .position).1 == (N.rowsAt m .carried).2 &&
        (N.rowsAt m .equation).1 == (N.rowsAt m .carried).2 + (N.rowsAt m .position).2 &&
        (N.rowsAt m .equation).2 == (if m == n then 0 else 1) &&
        (if m == 0 then (N.rowsAt m .carried).2 + (N.rowsAt m .position).2 == 0
          else decide (1 ≤ (N.rowsAt m .carried).2))

/-- Which tenants an item reads: by groups. -/
def Item.tenants (N : Numbers) : Item → List (Nat × Nat)
  | .constr m _ => N.group m
  | .pin m t => N.sent m t
  | .pinKept m => N.keptOf m
  | .tie m => N.sent m 0 ++ N.sent m 1
  | .pinI => [N.index]
  | .pinV => [N.w]
  | .pinW => []
  | .forms m _ _ => N.group m
  | .formsT m _ _ => N.sent m 0
  -- the lookup on the calls stands at piece 2 or 3, that on the digits at 7 or 8
  | .worth m k _ => if k ≤ 3 then N.sent m 0 else N.sent m 2 ++ N.sent m 0 ++ N.sent m 1
  | .wo _ => [N.index]
  | .totalB m => N.group m
  | .total m => N.group m
  | .row m _ => N.group m
  | .carry m => N.group m
  | .pile => [N.index]
  | .pileOne => [N.index]
  | .wrow => [N.w, N.index]
  | .unmarked => []

/-- A component of the witness. -/
inductive Comp where
  /-- the message with this number, OUTSIDE THE PAD's PLACES -/
  | msg (n : Nat)
  /-- the pad of tenant t of tree j: one component a copy -/
  | pad (j t : Nat)
  | tok
  | cells
  deriving DecidableEq, Repr

/-- **Which components of the witness an item reads.** arr: which message tenant t of tree j holds:
TO BE HANDED `Reading.arr` ITSELF (Johnson/Desc/Msg.lean). THE PADS ARE OVER-TOLD: every item is
booked as reading its tenants' pads, though only pins, sample rows and the carried claim (its term
on a kept member has a coefficient at the old copy's pad) do (a test on the plan that no cell, no
slot's mask entry and no other row's entry stands at a pad's place is not made here): safe for
`laysClear`, which asks that what is laid is read by nobody else. The token: the head's keys, as
long as they speak of the witness's token; and a layers' segment's identities and rider. The cells:
what names the weights outright, and what reads the stored table's message. TO BOOK MORE THAN A
SENTENCE READS IS SAFE wherever no block lays the component while the item rides: `laysClear` tries
that. TWO THINGS ARE LEFT UNBOOKED ON PURPOSE, AND BOOKING THEM WOULD BE NO CURE: the token at the
head's identities, rider and smallness (they ride across the reply's block, which lays it: that
these sentences do not turn with the witness's token is the filling's to show); and the pad of the
OWNER's seat where a segment reads another segment's array at a seam (that seat's closing or switch
lays it while the item rides: that no place named there is a pad's is the filling's to show).
-/
def Item.reads (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (i : Item) : List Comp :=
  ((i.tenants N).flatMap fun x => [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2]) ++
    (match i with
      -- the keys read the weights; the head's also the token; the first segment's identities the
      -- embedding's rows; a layers' segment's identities and rider are spelt at the request with
      -- the witness's token put in; a layers' segment's share is the same at the request itself
      -- (`share_put`, Johnson/Goal/Meaning/RowLocal.lean)
      | .constr m .lookCalls => .cells :: (if links[m]? == some .head then [.tok] else [])
      | .constr _ .lookCallsHeard => [.cells]
      | .constr m .idn =>
        (if m == 0 then [.cells] else []) ++ (if links[m]? == some .layers then [.tok] else [])
      | .constr m .rider => if links[m]? == some .layers then [.tok] else []
      -- the sentences at the heard points of the lookup on the calls read the stored table's
      -- message, but at an attention's segment, which has none
      | .worth m k _ => if k ≤ 3 && links[m]? != some .attention then [.cells] else []
      | .pinW => [.cells]
      | .wo _ => [.cells]
      | .pile => [.cells]
      | .pileOne => [.cells]
      -- the head's claim on the weights is summed over the witness's cells
      | .forms _ _ "weights" => [.cells]
      | .formsT _ _ "weights" => [.cells]
      | _ => [])

/-- THE ROW's OWN SEATS: the tenants whose pins the block at a place closes, and whose messages its
extractor lays: a closing: its group's but the kept ones (in the library the batching on a group is
what hands the pins back); the last proximity test: its own group's; the reply's block: none (it
lays the token). -/
def laysSeats (N : Numbers) (links : List ModelPart) (p : Place) : List (Nat × Nat) :=
  if !(rowOf links p).lays then []
  else match p.kind with
    | .K10 => (N.group (p.link.getD 0)).filter fun t => !(N.keptOf (p.link.getD 0)).contains t
    | .K12 => N.group links.length
    | _ => []

/-- THE SEATS WHOSE PADS ALONE the extractor of the block at a place lays: a switch: the copies that
the group in front of it has kept: it closes their pins (`pinKept`). -/
def laysPads (N : Numbers) (links : List ModelPart) (p : Place) : List (Nat × Nat) :=
  if !(rowOf links p).lays then []
  else match p.kind with
    | .K2 => N.keptOf (p.link.getD links.length - 1)
    | _ => []

/-- The extractor of the block at a place lays the token. -/
def laysTok (links : List ModelPart) (p : Place) : Bool := (rowOf links p).lays && p.kind == .K7

/-- Which components of the witness the extractor of the block at a place lays. -/
def laysOf (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (p : Place) : List Comp :=
  ((laysSeats N links p).flatMap fun x => [Comp.msg (arr x.1 x.2), Comp.pad x.1 x.2]) ++
    ((laysPads N links p).map fun x => Comp.pad x.1 x.2) ++
    (if laysTok links p then [.tok] else [])

/-- A TEST ON THE TABLE AND THE PLAN: at every row that lays, no two of the row's own seats have one
number (else, where their candidates differ, no witness can be laid), and no seat stands twice among
those whose pads are laid. -/
def laysNodup (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (ps : List Place) : Bool :=
  ps.all fun p => eachOnce ((laysSeats N links p).map fun x => (arr x.1 x.2, 0)) &&
    eachOnce (laysSeats N links p ++ laysPads N links p)

/-- A TEST ON THE TABLE AND THE PLAN: at every row that lays, the trees of the row's own seats were
sent in front of the block, and so were those of the seats whose pads it lays. base k: how many
trees the blocks in front of block number k send. -/
def laysFenced (base : Nat → Nat) (N : Numbers) (links : List ModelPart) (ps : List Place) : Bool :=
  ps.zipIdx.all fun q =>
    (laysSeats N links q.1 ++ laysPads N links q.1).all fun x => decide (x.1 < base q.2)

/-- The test beneath, at any laying: so that a control can hand it another than the table's. -/
def padsOnceBy (lays : Place → List Comp) (N : Numbers) (n : Nat) (ps : List Place) : Bool :=
  ((List.range (n + 1)).flatMap N.group).all fun x =>
    (ps.filter fun p => (lays p).contains (.pad x.1 x.2)).length == 1

/-- A TEST ON THE TABLE AND THE PLAN: THE PAD OF EVERY SEAT OF EVERY GROUP IS LAID BY JUST ONE ROW:
by its group's closing if the seat is not kept, by the next switch if it is, by the last proximity
test at the last group. THE INDEX MASKS' SEAT AND W's STAND IN NO GROUP OF THIS CHAIN: their pads
are laid beyond it. -/
def padsOnce (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (ps : List Place) : Bool :=
  padsOnceBy (laysOf arr N links) N links.length ps

/-- A TEST ON THE PLAN: THE COPIES OF ONE MESSAGE HAVE THEIR PADS AT ONE PLACE: the groups' seats
with one number have one key. key: those numbers of a seat's shape that say where its pad stands
(its mask rows; its main rows; their degree; its answers; the two codes' message lengths): a
letter here: the plan's run hands it. IT BEARS LOAD: a closing lays the later copy's WHOLE table at
the message's number: were a place the new copy's pad and not the old one's, "alike outside their
pads" would be false at an honest run, and a switch's row could be met by nobody, in silence. -/
def padSame (arr : Nat → Nat → Nat) (key : Nat → Nat → List Nat) (N : Numbers) (n : Nat) : Bool :=
  let seats := (List.range (n + 1)).flatMap N.group
  seats.all fun x => seats.all fun y =>
    arr x.1 x.2 != arr y.1 y.2 || key x.1 x.2 == key y.1 y.2

/-- The test beneath, at any rows: so that a control can hand it other rows than the table's. -/
def laysClearBy (rows : Place → BlockRow) (reads : Item → List Comp) (lays : Place → List Comp) :
    List Place → List Item → Bool
  | [], _ => true
  | p :: ps, O =>
    ((O.filter fun i => !(rows p).ins.contains i).all fun i =>
      (reads i).all fun t => !(lays p).contains t) &&
      laysClearBy rows reads lays ps (stepOpen O (rows p))

/-- A TEST ON THE TABLE AND THE PLAN: no open item that a block does not close reads a component
that the block's extractor lays. IT TESTS THE TABLE's OWN WORD: `Item.tenants` is by groups:
that these are the tenants which each kind's items read is not shown here. -/
def laysClear (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) :
    List Place → List Item → Bool :=
  laysClearBy (rowOf links) (fun i => i.reads arr N links) (laysOf arr N links)

/-- A TEST ON THE TABLE AND THE PLAN: every component of the witness that an item of `start` reads
is laid by some row: else the witness that the composed extractors give at the chain's first border
has a made-up component. A component that an item which is still open at the chain's end reads is
left out: it is laid beyond this chain. -/
def laysAll (arr : Nat → Nat → Nat) (N : Numbers) (links : List ModelPart) (ps : List Place) : Bool :=
  let beyond := ((openSets links ps (start links)).getLast?.getD []).flatMap fun i =>
    i.reads arr N links
  ((start links).flatMap fun i => i.reads arr N links).all fun k =>
    beyond.contains k || ps.any fun p => (laysOf arr N links p).contains k

/-! ## 6 The meaning -/

/-- **What an item says**, of the chain's record (P: what was handed to the chain: the public part,
WHICH HOLDS THE KEY FILE's RECORD; the state), the oracles and a witness. ONE FIELD A SORT OF ITEM:
a letter here; `mgAll` (Johnson/Desc/Sound/MgAll.lean) gives each, some in name alone, over open
parameters. The six fields on reading the oracles (pin · noColl · shown · held · pinW · decodes)
are given over Mathlib by the library's own notions (Johnson/Desc/Sound/MsgSig.lean); their plain
shadows are Johnson/Desc/Msg.lean's `PIN`, `NoColl`, `hasSmp`, `PINW`. EVERY FIELD READS A MESSAGE
THROUGH THE ONE ACCESSOR, BY SEAT (MsgSig.lean's): the pad's places off that copy's own pad, all
others off the message's number: NOBODY READS `w.msg` OR `w.pad` BARE: so the places that no pin
fixes (a message's number at a pad's place; a pad outside it) are read by nobody. WHICH "CELLS"
forms, formsT AND worth READ: the casts of the integers that the map to the model unpacks from the
committed symbols: under `constr m small` these are the committed cells. NO FIELD READS AN INDEX BY
A DEFAULT (a place without a row, a slot beyond the sizes, a cell outside its table) UNLESS A PUBLIC
Bool IN THE PROMISE SAYS THAT THE INDEX IS THERE. -/
structure Meaning (P W : Type) where
  /-- tenant t of tree j: the witness's message is what the committed word decodes to with the
  tenant's sample, as the record holds it -/
  pin : Nat → Nat → P × S → Strs → W → Prop
  /-- THE PROMISE beside it: no two members of the committed word's list answer the sample alike -/
  noColl : Nat → Nat → P × S → Strs → Prop
  /-- THE PROMISE: every leaf of the tenant's tree shows its symbol (a tree that is not sent reads
  as the zero word, WHICH IS A CODE WORD) -/
  shown : Nat → Nat → Strs → Prop
  /-- A Bool: the record holds the tenant's sample -/
  held : Nat → Nat → P × S → Bool
  /-- the witness's cells are what the stored table decodes to, with the key file's record -/
  pinW : P × S → Strs → W → Prop
  /-- THE PROMISE: the stored table decodes with the record: BY THE GUARDED DECODER (the top's own:
  nothing where two members of the word's list have the record's answers): so that "decodes" gives
  "no collision at the record's seed" by unfolding: the joint with the shared chain spends that.
  At a decoder without the guard there is a word that decodes and has a collision: that joint's
  premise could then not be proved. `pinW` reads the same decoder -/
  decodes : P × S → Strs → Prop
  /-- THE PROMISE, AT EVERY BORDER: a condition on the public record alone: the statement is "in
  order" (a fact on every group, every open row and every sample row of the statement, under which
  what a row says does not turn when the statement grows, and across the beginning of a test):
  WHOEVER FILLS `row` FILLS IT: NOT FILLED HERE; the
  closers of `row` ask it from the border. A Bool: so that an honest run can evaluate it. IT ALSO
  HOLDS THREE EQUATIONS, ASKED OF WHOEVER FILLS IT: the statement's codes, and the request's shape
  and the rows' layout IN THE CHAIN's OWN STATE OF THE CALLS (`S.check`), ARE THE DESCRIPTION's. NOT
  IN THE OPEN SEGMENT's OWN COPY (`S.live` inside a link), which stands in the part that a caller's
  block turns: "in order" must ride past every such block. That the copy has them too is for a
  public item of the segment, made where the segment is opened (out of these) -/
  inOrder : P × S → Bool
  /-- THE PROMISE: WHAT A PUBLIC ITEM SAYS OF THE PUBLIC RECORD: a Bool, so that an honest run can
  evaluate it at every border at which the item is open. Each is left to the kind that asks it
  (`PubRow.asks`): `frontOk` (behind the joining of the pending rows: the claim is made of a row;
  its columns fit W's table) and `evalLaid` (behind W's sending: the one open row lies on the own
  group that was made; the shared chain's point spends it): NOT FILLED HERE;
  the two Bools have run at no record. At `left` and `leftOn`, which have no Bool, `pubAll` gives
  true: what they say is `pubP`'s -/
  pub : Pub → P × S → Bool
  /-- THE PROMISE: WHAT A PUBLIC ITEM SAYS OF THE PUBLIC RECORD BESIDE ITS Bool: a Prop, still on
  the public record alone. IT BREAKS THIS TABLE's OWN RULE ("a Bool that has run"), ON THREE TERMS
  THAT KEEP ITS SPIRIT: (1) a clause has the form "THERE IS x SUCH THAT a body with code is true",
  and an honest walk evaluates THE BODY at its own x (the ledger in front and the rounds that it
  holds at that block); (2) SPAN ONE: made by block k, asked AND dropped by block k + 1: OR a
  keeping lemma through Lean for every kind that stands between maker and dropper; (3) True at
  every item but those named so (`left`, `leftOn`). THE DEFAULT IS True AT EVERY ITEM: a filling
  that leaves the field out promises nothing by it, IN SILENCE: it shows where the asker's first
  tie cannot be proved. IT IS ASKED AT THE OPEN PUBLIC ITEMS ALONE, not at those tied to open items
  -/
  pubP : Pub → P × S → Prop := fun _ _ => True
  /-- THE DOOR's FILLING: the public items that are no constructors of `Pub`, with their rows. SO
  THE OPEN PUBLIC SETS HANG ON THE MEANING: a theorem at two meanings speaks of two tables;
  `{ Mg with ... }` keeps the field -/
  more : More := {}
  constr : Nat → Part → P × S → Strs → W → Prop
  tie : Nat → P × S → Strs → W → Prop
  forms : Nat → Nat → String → P × S → Strs → W → Prop
  formsT : Nat → Nat → String → P × S → Strs → W → Prop
  worth : Nat → Nat → String → P × S → Strs → W → Prop
  wo : Nat → P × S → Strs → W → Prop
  totalB : Nat → P × S → Strs → W → Prop
  total : Nat → P × S → Strs → W → Prop
  row : Nat → RowClass → P × S → Strs → W → Prop
  /-- THE CODE WORD THAT IS NAMED BEHIND A CLOSING's FIRST ROUND IS PINNED BY NO SAMPLE: it stands
  under an "there is" INSIDE this meaning ("there is a code word within the joint radius of the
  group's word whose message meets the one row …"), never as a component of the witness. TWO
  CAUTIONS: its data move (between segments, the head's front, the finish, inside a
  segment): `S.frame` is the one reader; and filled by the library's joint behind the batching and
  the fold AT THE ARRANGED FORM it is false on a real proof beyond the target (the text's batched
  form is not 0 on the cube's free rows): the block with room is "arranged + the free rows' weights"
  -/
  carry : Nat → P × S → Strs → W → Prop
  /-- `fillK13` reads it through `S.rows`: behind the joining the old pile still lies, stale, in the
  walk's result -/
  pile : P × S → Strs → W → Prop
  pileOne : P × S → Strs → W → Prop
  /-- the rows on W hold: NO ROW OF THIS CHAIN OPENS THE ITEM: the letter stands for the joint with
  the shared chain, whose table takes it for the one open row on W's own group -/
  wrow : P × S → Strs → W → Prop

section
variable {P W : Type} (N : Numbers)

/-- **An item's meaning.** -/
def Item.holds (Mg : Meaning P W) : Item → P × S → Strs → W → Prop
  | .constr m p => Mg.constr m p
  | .pin m t => fun a y w => ∀ x ∈ N.sent m t, Mg.pin x.1 x.2 a y w
  | .pinKept m => fun a y w => ∀ x ∈ N.keptOf m, Mg.pin x.1 x.2 a y w
  | .tie m => Mg.tie m
  | .pinI => fun a y w => Mg.pin N.index.1 N.index.2 a y w
  | .pinV => fun a y w => Mg.pin N.w.1 N.w.2 a y w
  | .pinW => Mg.pinW
  | .forms m k r => Mg.forms m k r
  | .formsT m k r => Mg.formsT m k r
  | .worth m k r => Mg.worth m k r
  | .wo m => Mg.wo m
  | .totalB m => Mg.totalB m
  | .total m => Mg.total m
  | .row m c => Mg.row m c
  | .carry m => Mg.carry m
  | .pile => Mg.pile
  | .pileOne => Mg.pileOne
  | .wrow => Mg.wrow
  | .unmarked => fun a _ _ => a.2.failed = none

/-! ## 7 The promise -/

/-- Where the chain stands, by name. -/
inductive Stand where
  | between
  /-- a segment OF THIS SORT is open: the shared readers answer, and the sort's own part is there -/
  | link (sub : ModelPart)
  /-- the head's front: across the reply's round and the switch behind it -/
  | headFront
  | fin
  | mem
  deriving DecidableEq, Repr

/-- Where a state stands. -/
def standOf (s : S) : Stand :=
  match s.here with
  | .between => .between
  | .lay _ => .link .layers
  | .att _ => .link .attention
  | .head _ => if s.inLink then .link .head else .headFront
  | .fin _ => .fin
  | .mem _ => .mem

/-- **Where the chain is to stand at the border in front of the block at a place.** WRITTEN FROM THE
TEXTS, NOT FROM A RUN (State.lean's head and its functions enter…, openHead, leaveLink):
a segment's part of the state is born in the quiet part of its
first call's block and dies in the frame's block "cleared", AT EVERY SEGMENT, THE HEAD's TOO (there
the frame's clearing is Johnson/Desc/First/Close/TailHead.lean's text, seated at "cleared" as a
block of its own); the head's front lasts from the reply's block to the switch's; the finish from
the last switch; the members' places from the block that joins the pending rows. AN HONEST RUN TRIES
IT: IT CAN FAIL. -/
def standAt (links : List ModelPart) (p : Place) : Stand :=
  match p.link with
  | some m =>
    let sub := (links[m]?).getD .layers
    if p.piece ≤ 1 then .between
    else if sub == .head && p.piece == 2 then .headFront
    else .link sub
  | none =>
    match p.kind with
    | .K2 => .between
    | .K12 => .fin
    | .K13 => .fin
    | .K1 => .mem
    | _ => if p.piece == 0 then .between else .mem

/-- A count of rows may wait at two borders of a segment: behind the batching's draw, and behind the
runs behind the batching: the one equation, the closing's first block, pays
it. (WITH A WAIT AT THE FIRST OF THE TWO ALONE AN HONEST RUN WOULD SAY NO AT THE SECOND: said here
without a theorem.) -/
def mayWait (links : List ModelPart) (p : Place) : Bool :=
  match p.link with
  | some m =>
    let n := (kindsBeforeBatching ((links[m]?).getD .layers) (m == 0)).length
    p.piece == n + 2 || p.piece == n + 3
  | none => false

/-- **The book-keeping at a border**: a Bool on the state. p: the place of the block behind the
border; none: the chain's last border. IT ASKS: where the chain stands; that no count of rows waits
but at the two borders of `mayWait`; the open segment's SORT, AND ITS NUMBER (two segments of one
sort are else alike to it). NOT ASKED HERE: the counts against the plan's numbers. -/
def shapeAt (links : List ModelPart) (p : Option Place) (s : S) : Bool :=
  match p with
  | some p =>
    standOf s == standAt links p && (s.noneWaits || mayWait links p) &&
      s.link?.all fun L => p.link == some L.link
  -- where the pending rows are joined (both real plans); without a joining: NOT PROVIDED FOR
  | none => standOf s == .mem && s.noneWaits

/-- A TEST ON THE TABLE: AN ITEM THAT READS A SEGMENT's PART OF THE RECORD IS OPEN ONLY WHERE THE
BOOK-KEEPING SAYS THAT THIS PART IS THERE: at a border inside that segment at which a segment of its
sort is to stand open. (Else its meaning would read a part that is gone: idle in silence, or false.)
-/
def partsThere (links : List ModelPart) : List Place → List Item → Bool
  | [], O => O.all fun i => i.part.isNone
  | p :: ps, O =>
    (O.all fun i => match i.part with
      | none => true
      | some m => p.link == some m && standAt links p == .link ((links[m]?).getD .layers)) &&
      partsThere links ps (stepOpen O (rowOf links p))

/-- The sampled tenants whose pin is open at a border. O: the items that are open there. -/
def sampledIn (O : List Item) : List (Nat × Nat) :=
  O.flatMap fun i => match i with
    | .pin m t => N.sent m t
    | .pinKept m => N.keptOf m
    | .pinI => [N.index]
    | .pinV => [N.w]
    | _ => []

/-- A Bool: the record still holds the sample of every tenant whose pin is open. -/
def samplesHeld (Mg : Meaning P W) (O : List Item) (a : P × S) : Bool :=
  (sampledIn N O).all fun x => Mg.held x.1 x.2 a

/-- The segments of which a class of rows is open at a border. -/
def rowSegs (O : List Item) : List Nat :=
  (O.filterMap fun i => match i with
    | .row m _ => some m
    | _ => none).eraseDups

/-- How many rows the classes that are open at a border count in segment m's group's list. -/
def rowsDue (O : List Item) (m : Nat) : Nat :=
  O.foldl (fun k i => match i with
    | .row m' c => if m' == m && c.inList then k + (N.rowsAt m c).2 else k
    | _ => k) 0

/-- A Bool ON THE RECORD: of every segment of which a class of rows is open: its group is there (or
no class in the list is open yet), its test has not begun, ITS LIST HAS JUST AS MANY ROWS AS THE
OPEN CLASSES COUNT, and the row at each place of an open class is of the class's kind. The list's
length is the verifier's own doing, a function of the plan: so it stands in the promise; an honest
run can evaluate it, AND IT CAN FAIL.
-/
def rowsHeld (O : List Item) (s : S) : Bool :=
  (rowSegs O).all fun m =>
    match s.st.groups[N.groupAt m]? with
    -- a sample's class may be open while the message has joined no group yet
    | none => rowsDue N O m == 0
    | some G =>
      !G.inRun && G.rows.size == rowsDue N O m &&
        O.all fun i => match i with
          | .row m' c =>
            !(m' == m && c.inList) ||
              (List.range (N.rowsAt m c).2).all fun j =>
                (G.rows[(N.rowsAt m c).1 + j]?).any fun r => r.kind == c.kind
          | _ => true

/-- A Bool ON THE RECORD: WHERE THE BOOK STANDS: it holds as many trees as the plan says of the
blocks in front, and a place for every oracle message of the statement, OF WHICH THERE ARE AS MANY
AS THE PLAN SAYS. A sending's law names a
message BY ITS NUMBER; the promise's clauses on samples, leaves and collisions, the pins and
`membersHeld` name (tree, tenant): without this nobody can show that the new messages sit where
`Numbers.sent` and `Numbers.w` say. -/
def bookAt (p : Option Place) (s : S) : Bool :=
  s.book.trees.size == N.treesAt p && s.book.place.size == s.st.oracles.size &&
    s.st.oracles.size == N.msgsAt p

/-- A Bool ON THE RECORD: of every segment of which a class of rows is open and whose group is made:
THE GROUP's MEMBERS, read through the record's own book (oracle message ↦ tree, tenant), ARE JUST
THE SEGMENT's TENANTS WHOSE PINS ARE OPEN: else a closing's row would ask a pin, or a sample row, of
a test that never took the member in. (A message joins its group in the block that sends it: by an
honest run; a message without a sample is no member.) -/
def membersHeld (O : List Item) (s : S) : Bool :=
  (rowSegs O).all fun m =>
    match s.st.groups[N.groupAt m]? with
    | none => true
    | some G =>
      G.members.toList.all (fun o => (s.book.place[o]?).isSome) &&
        sameMembers (G.members.toList.filterMap fun o => s.book.place[o]?)
          ((List.range 3).flatMap fun t => if O.contains (.pin m t) then N.sent m t else [])

/-- Every public item that is open at the border, or tied to an item that is open there, holds of
the record. -/
def pubHeld (Mg : Meaning P W) (O : List Item) (Q : List Pub) (a : P × S) : Bool :=
  (Q ++ pubOfItems O).all fun q => Mg.pub q a

/-- **The promise at a border.** p: the place of the block behind it; none: the chain's last border.
O: the items that are open there. THE STORED TABLE DECODES WITH THE RECORD: AT EVERY BORDER, MARKED
OR NOT (no block turns that oracle or the record; the top's relation holds outright where it does
not; the shared chain's first promise is got from it). Beside it: A MARKED RECORD IS INSIDE EVERY
PROMISE; else: the book-keeping holds, the open rows' lists (`rowsHeld`) and the groups' members
(`membersHeld`) among it, and the statement is in order; the record still holds the sample of every
tenant whose pin is open; every such tenant's tree shows all its leaves, and no two members of its
list answer the sample alike. Q: THE PUBLIC ITEMS THAT ARE OPEN THERE: each holds of the record, and
so does each that is tied to an open item (`pubHeld`); LAST: what each open public item says beside
its Bool (`Meaning.pubP`). (An honest run can evaluate the book-keeping, "held" and the public
items' Bools; of `pubP` the body, at what the walk itself holds.) -/
def onAt (Mg : Meaning P W) (links : List ModelPart) (p : Option Place) (O : List Item) (Q : List Pub)
    (a : P × S) (y : Strs) : Prop :=
  Mg.decodes a y ∧
    (a.2.failed ≠ none ∨
      ((shapeAt links p a.2 && rowsHeld N O a.2 && membersHeld N O a.2 && Mg.inOrder a &&
          pubHeld Mg O Q a && bookAt N p a.2) = true ∧
        samplesHeld N Mg O a = true ∧
        (∀ x ∈ sampledIn N O, Mg.shown x.1 x.2 y ∧ Mg.noColl x.1 x.2 a y) ∧
        ∀ q ∈ Q, Mg.pubP q a))

end

end VerifiableInference.Desc.First
