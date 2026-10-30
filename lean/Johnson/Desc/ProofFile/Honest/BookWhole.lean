-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookWhole.lean: the tenth of the files that compute the book of coins
(`ProverCoinCounts`, Honest/Frame.lean): the whole book of a proof file's description as one definition: the
rows of all sendings, the switches' among them, and of a fold that sends its own fresh table; the
spending entries; the carrying entries; the cuts. From the description and the library's list of
sendings alone. It returns an error with a message: where one of these files' functions returns an
error, where a sending that it looks for by its label is not there, where the folded row's test has
no switch, where the second chain has no fold with a sending after it, where a fold outside the
shared chain sends its own fresh table, where a switch's main rows have free room (a class of coins
that these files do not count: Honest/BookSwitchRoom.lean), and where one of the book's own tests
fails (`ProverCoinCounts.word`): so what it returns has passed them. Executable definitions; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

  `mergesByName`   which masked sumchecks are merges, read off the kinds and the counts
  `lastLink`   the number of the last group: the greatest l in a label "link l, …"
  `firstCodes`   the two codes of a proximity test's first stage, by the test's name
  `bookRaw`, `ProverCoinCounts.checked`, `bookWhole`   the book as it is computed; the book's own tests; the
     book

The groups outside the chain of segments (docs/format/09-key-and-leaf-files.md, its terms): the
folded row's test: the folded row and the shared split's mask message; Omega's: all messages of
Omega's sending; a request's own: the index-mask message, W with what is sent with it, and Omega.

Limits.
  * The split case alone: it looks for the sendings "the folded row", "Omega" and "W" and for the
    four tests by the library's labels, and returns an error where one is lacking.
  * `mergesByName` reads kinds and counts: a masked sumcheck of K4 or K11 with one end value; a
    masked sumcheck of K13. Its docstring names the texts outside this file on which that rests.
    Nothing compares its list with the plan's own data; no `#guard` and no test of the book names
    it. It is meant for a proof file's first chain alone.
  * No test in this file evaluates `bookWhole`: it needs the public files' data; a test program
    does.
  * An empty list from `ownFreshIn` (Honest/BookOwnFresh.lean) says less than "no fold sends such a
    table": that function silently drops a fold at round 0, and one after which it finds nothing.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookOwnFresh
import Johnson.Desc.ProofFile.Honest.BookSwitchRoom
import Johnson.Desc.ProofFile.Honest.BookAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi S Cl : Type}

/-- **Which masked sumchecks are merges: read off the kinds and the counts.** It rests on three
texts outside this file. (1) The entry of the index-mask message under a merge's end value is taken
where a link is cleared: `clearWith` (Johnson/Desc/First/Walk/Frame.lean) calls the function `row`
that it is handed; at the head's link that is `pendingRowO` (Johnson/Desc/First/Close/TailHead.lean;
Johnson/Desc/First/Pend/Row.lean), which takes the next free entry (`takeEntry`); where a layers'
link hands it over is not traced. By the docstring of `planFlag` (Walk/Frame.lean)
every link but an attention link leaves such a row. (2) In K4's table of rounds (`rounds`,
OnBytes/Desc/First/K4/Rounds.lean) the last masked sumcheck, the merge, is written with one end
value. Of the six others three are written with 2 and one with at least 3; that `ledNO h.xl * y.NI`
and `nEndT y` are not 1 is not held here. (3) K13's `batt` (Johnson/Desc/K13/Text.lean) takes
`Batt.masksOf kCol` = 1 + 2 kCol entries of that message, as many as its sumcheck sends. That the
definition agrees with these three texts and with the format's page (docs/format/11-1-machinery.md,
"The merge") is by reading alone, the page's half by report. If one of the three texts turns, this
definition goes wrong in silence. -/
def mergesByName (bs : List (Block S Cl)) : Merges :=
  let parts := bs.flatMap planParts
  { ends := (parts.filter fun p => p.isSum && p.endScalars == 1 &&
      (p.addr.place.kind == .K4 || p.addr.place.kind == .K11)).map (·.addr)
    lone := (parts.filter fun p => p.isSum && p.addr.place.kind == .K13).map (·.addr) }

/-- The number of the last group. -/
def lastLink (c : Johnson.G.ChainSends) : Option Nat :=
  (c.sends.filterMap fun s => linkOf s.label).foldl (fun m l => some ((m.getD 0).max l)) none

/-- The two codes of the sending under a label. -/
def codesUnder (c : Johnson.G.ChainSends) (label : String) : Option (OnBytes.Code × OnBytes.Code) :=
  (c.sends.find? fun s => s.label == label).bind fun s => groupCodes c.codes s.sent

/-- **The two codes of a test's first stage.** `p0`, `p1`: the first and the shared chain's
sendings. -/
def firstCodes (p0 p1 : Johnson.G.ChainSends) (t : String) :
    Option (OnBytes.Code × OnBytes.Code) :=
  if t == "the last group's test" then
    (lastLink p0).bind fun l => codesUnder p0 s!"link {l}, moment 0"
  else if t == "the folded row's test" then codesUnder p1 "the folded row"
  else if t == "Omega's test" then codesUnder p1 "Omega"
  else if t == "the own test" then codesUnder p0 "W"
  else none

universe u in
/-- A value that must be there. -/
def due? {α : Type u} (what : String) : Option α → Except String α
  | some a => .ok a
  | none => .error (what ++ " is not found")

/-- The whole book as it is computed, before its own tests. `p0`, `p1`, `p2`: the library's sendings
of the proof's three chains. The carrying entries are appended in this order: the chain of
segments'; the folded row's group's; Omega's; the request's own; then those of the folds that send
their own fresh table. `lend` (Honest/Frame.lean) reads a part's entries in the book's order. -/
def bookRaw (F : FileDescription Xi) (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    Except String ProverCoinCounts := do
  let B ← spendingBook F p0 p1 p2 M
  let later := F.second.blocksInOrder.flatMap (·.rounds)
  let m0 ← sentIn F.first.blocksInOrder p0 later
  let m1 ← sentIn F.shared.blocksInOrder p1
  let first := firstCodes p0 p1
  let r0 ← switchRows F.first.blocksInOrder p0 first
  let r1 ← switchRows F.shared.blocksInOrder p1 first
  let r2 ← switchRows F.second.blocksInOrder p2 first
  for c in [p0, p1, p2] do
    match ← mainRoomFault c first with
    | none => pure ()
    | some l => throw (l ++ ": its main rows have free room, or too few places: not counted")
  let P1 := planOf F.shared.blocksInOrder
  let under (ms : List SentMsg) (label : String) := ms.filter fun m => m.label == label
  let fr := under m1 "the folded row"
  let om := under m1 "Omega"
  let w := under m0 "W"
  let seg ← segmentCarries (planOf F.first.blocksInOrder) m0
  let iF ← due? "the folded row's sending" (fr.head?.map (·.round))
  let cF ← groupCarries P1 iF (fr.filter (!·.fresh) ++ om.filter (·.masks)) (fr.find? (·.fresh))
  let iO ← due? "the folded row's test's last switch"
    ((((seedRounds F.shared.blocksInOrder).zip p1.sends).filter fun x =>
      testOf x.2.label == "the folded row's test").getLast?.map (·.1))
  if om.isEmpty then throw "Omega's sending is not found"
  let cO ← groupCarries P1 iO om none
  if w.isEmpty then throw "W's sending is not found"
  let pq ← due? "the second chain's first fold, with a sending behind it"
    (behindFold (planOf F.second.blocksInOrder) 0)
  let cW := carryPair pq.1 pq.2
    (m0.filter (·.masks) ++ w.filter (!·.fresh) ++ om.filter (!·.masks)) (w.find? (·.fresh))
  let own := ownFreshIn F.shared.blocksInOrder
  if !(ownFreshIn F.first.blocksInOrder).isEmpty || !(ownFreshIn F.second.blocksInOrder).isEmpty then
    throw "a fold outside the shared chain sends its own fresh table: its mask code is not laid"
  let tail ← due? "the shared chain's mask code" ((codesUnder p1 "Omega").map (·.2.r))
  pure
    { B with first := B.first ++ r0, shared := B.shared ++ r1 ++ own.map (·.row tail)
             second := B.second ++ r2
             ahead := B.ahead ++ seg ++ cF ++ cO ++ cW ++ own.map (·.carry tail) }

/-- A book that fails none of its own tests at a description; else an error that names the first
test that fails. -/
def ProverCoinCounts.checked (F : FileDescription Xi) (W : ProverCoinCounts) : Except String ProverCoinCounts :=
  match W.word F with
  | none => .ok W
  | some t => .error ("the book fails its own test: " ++ t)

/-- **The whole book**: `bookRaw`, then the book's own tests. -/
def bookWhole (F : FileDescription Xi) (p0 p1 p2 : Johnson.G.ChainSends) (M : Merges) :
    Except String ProverCoinCounts :=
  (bookRaw F p0 p1 p2 M).bind (ProverCoinCounts.checked F)

/-- A sending of no message, for the tests. -/
def toySend (label : String) : Johnson.G.Sending :=
  ⟨0, label, [], { name := "" }, { name := "" }⟩

#guard lastLink ⟨"proof", 0, toyCodes, [toySend "link 0, moment 0", toySend "link 0, moment 1",
  toySend "link 7, moment 0", toySend "W"]⟩ == some 7
#guard lastLink ⟨"proof", 0, toyCodes, [toySend "W"]⟩ == none

end ProofFile.Honest
