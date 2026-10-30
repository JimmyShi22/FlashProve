-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/ParsedKnown.lean: tests of the declared structure (Decl/Declared.lean, Fmt/Parsed.lean) on
made-up values. What is checked: `#guard` lines, when the file compiles, on a table's shape, on
sources of a chain's items and on the bytes of made-up rounds. The same structure at the toy key and
entry that the programs wrote: OnBytes/Entry/TestRecordToyDeclared.lean. No theorem.
-/
import Fmt.Parsed
import Fmt.ParamsReadLaws
import Fmt.M3Entry
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M1Types
import Fmt.M3ParOf

namespace Fmt
namespace ParsedKnown
open M3

/-- the toy tables' shape -/
def shapeT : TableShape := ⟨14, 803, 1001, 3, 1, 40⟩

/-- a tree of the chain's own, named; the toy's chain takes none over -/
def srcT : Src → TreeSource
  | .own n => .own n
  | .given _ _ => .taken 0 0

/-- eight made-up answers -/
def eight : List Ext := (List.range 8).map fun i => (UInt64.ofNat i, 7, UInt64.ofNat (i * i))

/-- the record with eight made-up answers -/
def with8 (F : EntryParsed) : EntryParsed := { F with table := { F.table with answers := eight } }

/-- the rounds changed by g -/
def atRounds (g : List RoundParsed → List RoundParsed) (F : EntryParsed) : EntryParsed :=
  { F with link := { F.link with rounds := g F.link.rounds } }

/-- round i changed by g -/
def atRound (i : Nat) (g : RoundParsed → RoundParsed) : EntryParsed → EntryParsed :=
  atRounds fun l => l.zipIdx.map fun r => if r.2 == i then g r.1 else r.1

/-- opening j of round i changed by g -/
def atOpen (i j : Nat) (g : OpenParsed → OpenParsed) : EntryParsed → EntryParsed :=
  atRound i fun r => { r with opens := r.opens.zipIdx.map fun o => if o.2 == j then g o.1 else o.1 }

/-- the first column with its salt changed by g -/
def atCol (g : List UInt64 × ByteArray → List UInt64 × ByteArray) (o : OpenParsed) : OpenParsed :=
  { o with cols := o.cols.zipIdx.map fun c => if c.2 == 0 then g c.1 else c.1 }

/-- a word that spells no element of the second field -/
def big : UInt64 := 18446744073709551615

/-- an answer in the place of an element, and the other way round: the same bytes -/
def swapKind : ItemValue → ItemValue
  | .e x => .answer x
  | .answer x => .e x
  | g => g

/-- The honest record with one thing changed: none of these fits. Round 3 (from 0) is LINK, with a
nonce and two openings; round 0 has no byte in the file; round 1 sends a root; round 2 answers. The
first two are written back to the honest file's bytes. -/
def bad : List (EntryParsed → EntryParsed) := [
  atRound 2 fun r => { r with vals := r.vals.map swapKind },
  atRounds fun l => l ++ [⟨[], none, [], []⟩],
  fun F => { F with head := headOf tagKey .two },
  fun F => { F with table := { F.table with root := F.table.root.extract 0 31 } },
  fun F => { F with table := { F.table with answers := [(1, 2, 3)] } },
  fun F => { F with link := { F.link with rand := none } },
  fun F => { F with link := { F.link with rand := some (zeroBytes 33) } },
  atRounds fun l => l.dropLast,
  atRound 0 fun r => { r with vals := [.e (1, 2, 3)] },
  atRound 0 fun r => { r with nonce := some 0 },
  atRound 1 fun r => { r with vals := [.e (1, 2, 3)] },
  atRound 2 fun r => { r with vals := r.vals.map fun _ => .answer (big, 0, 0) },
  atRound 3 fun r => { r with nonce := none },
  atRound 3 fun r => { r with listed := [1] },
  atRound 3 fun r => { r with opens := r.opens.take 1 },
  atOpen 3 0 fun o => { o with cols := [] },
  atOpen 3 0 fun o => { o with cols := o.cols ++ o.cols.take 1 },
  atOpen 3 1 (atCol fun c => (c.1.dropLast, c.2)),
  atOpen 3 1 (atCol fun c => (c.1, c.2 ++ zeroBytes 8)),
  atOpen 3 1 (atCol fun c => (c.1.map fun _ => big, c.2)),
  atOpen 3 1 fun o => { o with given := o.given.map fun d => d.extract 0 31 } ]

/-- a made-up item "the test on the table": the toy's shape, then one word -/
def testT : ByteArray := cat (shapeT.words.map u64n) ++ u64 5

/-- a round that ends in a seal -/
def sealR : DeclaredRound := ⟨{ name := "SEAL" }, [], []⟩

/-- Made-up chains of a key file: the first two send a root each, the shared chain opens a stored
table, the second opens the two trees. -/
def keyT : ThreeDecl where
  first :=
    { label := 0x46524d02, record := true, rand := .inFile,
      others := [("index-mask message", u64 0), ("ranges", u64 0),
        ("binding tree", u64 0 ++ u64 40), ("codes", u64 9), ("the test on the table", testT)],
      rounds := [⟨{ name := "SEND seed", msg := 32, roots := 1, drawE := 2, drawNZ := 1 }, [], []⟩,
        sealR] }
  bind := ⟨0, 40⟩
  shared :=
    { label := 0x4c494e01, rand := .item 1,
      others := [("codes", u64 9), ("the test on the table", testT)],
      rounds := [⟨{ name := "SEND seed", msg := 32, roots := 1, drawE := 2, drawNZ := 1 }, [], []⟩,
        ⟨{ name := "LOC", poss := 2, logN := 14 }, [⟨⟨14, 8, true, 0⟩, 40, 0, 0, 2⟩], []⟩, sealR] }
  second :=
    { label := 0x4c494e02, rand := .inFile, others := [], firstTree := 2,
      rounds := [⟨{ name := "CS", poss := 1, logN := 1 }, [],
        [(⟨1, 1, false, 0⟩, .taken 0 0), (⟨1, 1, false, 0⟩, .taken 1 0)]⟩] }

/-- made-up chains of a proof file: the key's, under a proof's three labels, items and binding tree
-/
def proofT : ThreeDecl :=
  { keyT with
    bind := ⟨2, 40⟩
    shared := { keyT.shared with label := 0x46524d03 }
    second := { keyT.second with label := 0x46524d04 }
    first := { keyT.first with
      label := 0x46524d01, record := false,
      others := [("codes", u64 9), ("the test on the table", testT), ("request's shape", u64 0),
        ("layout", u64 0), ("links' identifiers", u64 0), ("pending rows", u64 1),
        ("binding tree", u64 2 ++ u64 40)] } }

/-- the made-up chains with one thing changed: none of these passes -/
def badKey : List ThreeDecl := [
  { keyT with first := { keyT.first with label := 0x46524d01 } },
  { keyT with first := { keyT.first with record := false } },
  { keyT with shared := { keyT.shared with rand := .item 0 } },
  { keyT with bind := ⟨0, 48⟩ },
  { keyT with bind := ⟨0, 48⟩, first := { keyT.first with others := keyT.first.others.map fun x =>
      if x.1 == "binding tree" then (x.1, u64 0 ++ u64 48) else x } },
  { keyT with bind := ⟨1, 40⟩ },
  { keyT with shared := { keyT.shared with
      others := [("codes", u64 8), ("the test on the table", testT)] } },
  { keyT with shared := { keyT.shared with
      others := [("codes", u64 9), ("the test on the table", testT ++ u64 0)] } },
  { keyT with second := { keyT.second with others := [("codes", u64 9)] } },
  { keyT with second := { keyT.second with firstTree := 3 } },
  { keyT with first := { keyT.first with firstTree := 1 } },
  { keyT with shared := { keyT.shared with label := 0x4c494e02 } },
  { keyT with second := { keyT.second with label := 0x4c494e01 } },
  { keyT with shared := { keyT.shared with record := true } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored.map fun t => { t with sh := { t.sh with W := 4 } } } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := [] } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored.map fun t => { t with count := 1 } } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored.map fun t => { t with item := 1 } } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored.map fun t => { t with lo := 1 } } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored ++ r.stored } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      if r.entry.name == "LOC" then { r with opens := [(⟨1, 1, false, 0⟩, .own 0)] } else r } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.filter fun r =>
      r.entry.name != "LOC" } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored.map fun t => { t with sh := { t.sh with stored := false } } } } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.map fun r =>
      { r with stored := r.stored.map fun t => { t with sh := { t.sh with tree := 7 } } } } },
  { keyT with first := { keyT.first with rounds := keyT.first.rounds.map fun r =>
      { r with stored := [⟨⟨14, 8, true, 0⟩, 40, 0, 0, 0⟩] } } },
  { keyT with second := { keyT.second with rounds := keyT.second.rounds.map fun r =>
      { r with opens := [] } } },
  { keyT with second := { keyT.second with rounds := keyT.second.rounds.map fun r =>
      { r with entry := { r.entry with poss := 0 }, opens := [] } } },
  { keyT with second := { keyT.second with rounds := [] } },
  { keyT with second := { keyT.second with rounds := keyT.second.rounds ++ [sealR] } },
  { keyT with second := { keyT.second with rounds := keyT.second.rounds.map fun r =>
      { r with opens := r.opens ++ [(⟨1, 1, false, 101⟩, .own 99)] } } },
  { keyT with first := { keyT.first with rounds := keyT.first.rounds.dropLast } },
  { keyT with shared := { keyT.shared with rounds := keyT.shared.rounds.dropLast } },
  { keyT with first := { keyT.first with rounds := keyT.first.rounds.map fun r =>
      { r with entry := { r.entry with drawNZ := 0 } } } },
  { keyT with first := { keyT.first with rounds :=
      [⟨{ name := "FOO", msg := 32, roots := 1 }, [], []⟩, sealR] } },
  { keyT with first := { keyT.first with rounds :=
      [⟨{ name := "SEND seed", msg := 32, roots := 1, drawE := 2, drawNZ := 1, rows := 2 ^ 64 },
        [], []⟩, sealR] } },
  { keyT with first := { keyT.first with rounds :=
      [⟨{ name := "SEND seed", msg := 40, roots := 1, drawE := 2, drawNZ := 1 }, [], []⟩, sealR] } },
  { keyT with first := { keyT.first with others := keyT.first.others.reverse } },
  { keyT with second := { keyT.second with rounds := [⟨{ name := "CS", poss := 1, logN := 1 },
      [], [(⟨1, 1, false, 1⟩, .taken 0 1)]⟩] } },
  { keyT with second := { keyT.second with rounds := [⟨{ name := "CS", poss := 1, logN := 1 },
      [], [(⟨1, 1, false, 0⟩, .taken 2 0)]⟩] } },
  { keyT with second := { keyT.second with rounds := [⟨{ name := "CS", poss := 1, logN := 1 },
      [], [(⟨1, 1, false, 1⟩, .taken 0 0)]⟩] } },
  { keyT with shared := { keyT.shared with rounds := [⟨{ name := "CS", poss := 1, logN := 1 },
      [], [(⟨1, 1, false, 0⟩, .taken 0 0)]⟩] } } ]

/-- a made-up chain of one round, for the writers of a key file and a proof file -/
def one (x : UInt64) (rand : Option ByteArray) : ChainParsed := ⟨rand, [⟨[.word x], none, [], []⟩]⟩

end ParsedKnown

open ParsedKnown M3

/-- The words of the plan are the library's `Entry.words` of the plan's entries, by definition. -/
example (D : Declared) (c : ChainDecl) :
    D.planWords c = (D.plan c).entries.map fun e => (e.name, e.words) := rfl

#guard headOf tagEntry .one != headOf tagEntry .two
#guard (namesElems ++ namesJoin ++ namesSeeds ++ namesPositions ++ namesEntries ++ namesSealed ++ namesNothing).length == 29 && (namesElems ++ namesJoin ++ namesSeeds ++ namesPositions ++ namesEntries ++ namesSealed ++ namesNothing).eraseDups.length == 29 && ((namesElems ++ namesJoin ++ namesSeeds ++ namesPositions ++ namesEntries ++ namesSealed ++ namesNothing).map fun n => (kindOf n).map (·.num)) == (List.replicate 15 (some 1) ++ List.replicate 2 (some 2) ++ [some 3] ++ List.replicate 4 (some 4) ++ [some 5, some 6] ++ List.replicate 5 (some 7)) && kindOf recordName == none && kindOf "FOLD" == none
#guard shapeT.ok && ([{ shapeT with a := 0 }, { shapeT with a := 61 }, { shapeT with message := 0 }, { shapeT with tail := 2 ^ 14 }, { shapeT with logRows := 41 }, { shapeT with answers := 268 }, { shapeT with saltBytes := 41 }].map TableShape.ok) == List.replicate 7 false && ({ shapeT with answers := 267 } : TableShape).ok && !(⟨32, 2 ^ 31, 0, 40, 2 ^ 19, 40⟩ : TableShape).ok && (⟨32, 2 ^ 31, 0, 40, 2 ^ 18, 40⟩ : TableShape).ok && (EntryStm.bytes ⟨⟨zero32, eight⟩, ⟨zero32, eight⟩⟩).size == 160 + 48 * 8
#guard TreeSource.src [([zero32, pattern 32], pattern 32 5 1), ([pattern 32 2 2], pattern 32 3 3)] (.taken 0 1) == some (.given (pattern 32) (pattern 32 5 1)) && TreeSource.src [([zero32], zero32)] (.taken 0 1) == none && TreeSource.src [([zero32], zero32)] (.taken 1 0) == none && TreeSource.src [] (.own 3) == some (.own 3)
-- (j') the form of a round under a plan that lists positions of two bytes, at made-up values: it fits; not increasing, out of the range, more than the draws, none, wider than its bytes: it does not; a nonce wider than its two bytes does not
#guard (let S : PlanSetting := ⟨.two, 40, 2, 2, 1, 1⟩; let r : DeclaredRound := ⟨{ name := "CS", work := 4, poss := 3, logN := 20 }, [], []⟩; ([⟨[], some 258, [1, 2, 515], []⟩, ⟨[], some 258, [2, 1], []⟩, ⟨[], some 258, [1, 1048576], []⟩, ⟨[], some 258, [1, 2, 3, 4], []⟩, ⟨[], some 258, [], []⟩, ⟨[], some 258, [1, 65536], []⟩, ⟨[], some 65536, [1], []⟩] : List RoundParsed).map fun x => x.fits S r) == [true, false, false, false, false, false, false]
-- (k) the statements of a key file's and a proof file's chains, item by item, at made-up values; the next token as an element; the head's number against the statement's
#guard (⟨zero32, [(1, 2, 3)]⟩ : TableSt).item == tableItem "table" zero32 [(1, 2, 3)] && sharedStm ⟨zero32, []⟩ (pattern 32) == tableItem "table" zero32 [] ++ item bindRootName (pattern 32) && (⟨⟨zero32, []⟩, 258, pattern 708, pattern 40 5 1, (7, 0, 0)⟩ : ProofStm).bytes == tableItem "table" zero32 [] ++ item "stored copy" (u64 258) ++ item "request" (u64 708 ++ pattern 708) ++ item "the request file's words" (u64 40 ++ pattern 40 5 1) && (item "request" (text (pattern 708))).size == 8 + 7 + 8 + 716 && (item "the request file's words" (text (pattern 40 5 1))).size == 8 + 24 + 8 + 48 && hex (ascii "the request file's words") == "74686520726571756573742066696c65277320776f726473" && (⟨zero32, [1, 2], 7⟩ : UserStm).reply == (7, 0, 0)
-- the two strings of bytes in each other's places give another statement
#guard (⟨⟨zero32, []⟩, 258, pattern 708, pattern 40 5 1, (7, 0, 0)⟩ : ProofStm).bytes != (⟨⟨zero32, []⟩, 258, pattern 40 5 1, pattern 708, (7, 0, 0)⟩ : ProofStm).bytes && ({ table := ⟨zero32, []⟩, copy := 258, request := pattern 708, words := pattern 40 5 1, reply := (7, 0, 0) } : ProofStm) == ⟨⟨zero32, []⟩, 258, pattern 708, pattern 40 5 1, (7, 0, 0)⟩
#guard ProofParsed.copyFits ⟨⟨zero32, []⟩, 258, pattern 8, pattern 8, (7, 0, 0)⟩ { (default : ProofParsed) with copy := 258 } && !ProofParsed.copyFits ⟨⟨zero32, []⟩, 258, pattern 8, pattern 8, (7, 0, 0)⟩ { (default : ProofParsed) with copy := 259 }

end Fmt
