-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/Flat.lean: a transcript of one lookup as plain data, what the program's lookup verifier
reads of it, and what that verifier hands on, again as plain data.

Why. A description of the lookup in the library's typed form is to be compared with the program's
verifier, Lkp.verify (OnBytes/Iop/Lkp.lean). Such a description has a type of transcripts of its
own. This file gives a type that belongs to no description (Flat): for each round the elements sent
and the elements drawn, and beside them the three vectors that the least caller has sent before the
lookup (of the keys those that are not padding). A description lifts a Flat to its own transcript
(so `Tw.lift`, OnBytes/Tie/Pv/Lookup/Out/TwLift65.lean). This file takes a Flat to the program's
side.

The least caller. Three oracle messages, all sampled before the lookup begins: number 0 holds the
keys (a key is an entry), number 1 the bits of the multiplicities (bit j of the count of row t at
the index j + 2^mu t), number 2 one mask row, from which the lookup takes all its mask entries. All
three are members of group 0. The sending and the sampling are no rounds of a Flat: the statement is
made up with the three messages marked as sampled, after the pattern of OnBytes/Iop/TestLkp.lean
(statement).

THE MADE-UP STATEMENT IS NOT ONE THAT THE PROGRAM'S OWN SENDING CAN LEAVE. The sending block lays
the entries that mask an answer to a sample (the pad) into a message's mask rows or, if it has none,
at the end of its last main row (Send.pad, OnBytes/Iop/Send.lean). Messages 0 and 1 have main rows
alone, over the extension field, and one answer: the pad of each would be the last place of its row.
In message 1 that is a bit of the multiplicities, on which three of the lookup's rows have
coefficients (one of them a constant that is not 0), and Blk.addRow would refuse these rows. In
message 0 it is the last key; where that is a place of padding and the rows have the coefficient 0
on it (`PaddingOut`, OnBytes/G4/RunLaws.lean), message 0 would not stand in the way. Here Oracle.pad
is empty in all three messages, and that test of Blk.addRow is empty. A sampled message would also
hold its sample rows; here it holds none.

What Lkp.verify reads.
 - The public inputs (Lkp.Public), the routine that lays a vector on the multiplicities into a row,
   the numbers of the message with the mask entries and of the group: `block`.
 - From the context (Blk, OnBytes/Iop/Ground.lean): the plan's entries and the statement (`start`),
   and the view's rounds (`Flat.view`): for each round the items read, each an element, and the
   record of what was drawn, of which only the elements are filled.

What it hands on. The rows that it adds to the group, and one claim on the keys, of which the caller
makes a row (`keysRow`) and adds it too. `endClaims` reads each row as coefficients on the entries
of the three vectors and a target (EndClaim).

What decides. At this caller, on a view of the plan's shape, Lkp.verify fails on no value that is
sent or drawn (under premises on the public inputs a law: portOn_ok, OnBytes/G4/RunLaws.lean;
elsewhere by a reading of the block's text). A sumcheck's equations fix the coefficients that are
not sent, and what it finds goes into rows. The one test on values in the course (line,
OnBytes/Iop/Psc.lean: the two claims of a level are at one point) compares two copies of one point.
(At a caller with pads the test of Blk.addRow on them is a second test on values.) In the protocol
the blocks that follow test the rows against the committed vectors. Here the vectors are at hand.
`judge` takes forms with targets, whoever made them, and the three vectors, and says whether all
forms meet their targets or which is the first that does not. `portVerdict` is `judge` on the
program's own end claims.

Two rules that the block does not test, because the stage before it sees to them: the words of every
element are below p, and the element drawn in a round "PSC Y" is not 0. Plain data can break both.
`Flat.fits` tests the second rule. It tests the first rule for the words of the three vectors and
for the drawn words. It does not test the size of the words of an element that a round sends. What
follows from that, by a reading of the texts: in the field's arithmetic a word that is not below p
counts as its residue (OnBytes/Base.lean), so `accepts` can say yes to plain data with a sent word
that the strict reader of a chain's bytes would refuse. And a sent element can go into a row's
target as it stands: the value shown at the end of the last sumcheck does (step 6 of Lkp.run,
OnBytes/Iop/Lkp.lean; pointRow, OnBytes/Iop/Psc.lean). If a word of that value is not below p,
`EndClaim.fits` refuses the row's claim, and `portVerdict` says `unfit` though t.fits S is true and
the run has gone through.

Main definitions: FlatRound, Flat, keysMessage, planesMessage, masksMessage, theGroup, served,
paddingRow, isPadding, realPlaces, keyCount, planeBits, entries, claimCount, FlatRound.fits,
Flat.vectorsFit, Flat.fits, FlatRound.rv, elementOfGot, FlatRound.ofRV, Flat.view, statement, start,
keysRow, block, portOn, EndClaim, EndClaim.fits, onCaller, ofRow, endClaims, EndClaim.holds,
Verdict, judge, failing, portVerdict, accepts.

Not claimed. Nothing on soundness. Nothing on lookups that `served` refuses (several parts, tree
numbers, a shift, planes that are not real, other messages read than the least caller's two).
`served` REFUSES EVERY LOOKUP THAT THE PROGRAM'S OWN CALLER MAKES: `Wf.lookupOf`
(OnBytes/Iop/Wf.lean) lays one message as read, and `served` asks for two. This file holds no
theorem. Laws: OnBytes/G4/FlatLaws.lean, OnBytes/G4/RunLaws.lean.


-/
import OnBytes.Iop.Lkp

namespace OnBytes.G4

/-! ## The plain data -/

/-- One round: the elements that the prover sends, in their order, and the elements that the
verifier draws after them, in the order in which they are drawn. -/
structure FlatRound where
  /-- the elements sent -/
  sent : List E
  /-- the elements drawn -/
  drawn : List E
  deriving DecidableEq, Repr, Inhabited

/-- A transcript of one lookup with the least caller's three vectors. -/
structure Flat where
  /-- the rounds, in the plan's order -/
  rounds : List FlatRound
  /-- the keys that are not padding, by increasing key number (realPlaces) -/
  keys : List E
  /-- the bits of the multiplicities: bit j of the count of row t at the index j + 2^mu t -/
  planes : List E
  /-- the mask row's entries that the lookup takes, in the order in which it takes them -/
  masks : List E
  deriving DecidableEq, Repr, Inhabited

/-! ## The least caller -/

/-- The number of the oracle message with the keys. -/
def keysMessage : Nat := 0

/-- The number of the oracle message with the bits of the multiplicities. -/
def planesMessage : Nat := 1

/-- The number of the oracle message with the mask row. -/
def masksMessage : Nat := 2

/-- The number of the group. -/
def theGroup : Nat := 0

/-- The lookups that the least caller serves: well-formed, one part, no tree numbers, no shift, all
planes real, and the messages read are the caller's first two. With no tree numbers a well-formed
lookup has one block of trees, and that block has a function (Public.keysOK, Public.onlyPadding). -/
def served (S : Lkp.Public) : Bool :=
  S.ok && S.parts.length == 1 && S.g == 0 && !S.shifted && S.live == 0 &&
  S.readFrom == [keysMessage, planesMessage]

/-- The number of the row that key number i holds, if it is a place of padding: if it lies in one of
the cubes into which the program cuts a run of padding (Lkp.cubesOf). -/
def paddingRow (S : Lkp.Public) (i : Nat) : Option Nat :=
  (S.padding.find? fun p =>
    p.part == 0 && (Lkp.cubesOf p S.firstBits).any fun c => (i &&& c.mask) == (c.value &&& c.mask)
    ).map (·.row)

/-- Key number i is a place of padding. -/
def isPadding (S : Lkp.Public) (i : Nat) : Bool := (paddingRow S i).isSome

/-- The numbers of the keys that are not padding, increasing. -/
def realPlaces (S : Lkp.Public) : List Nat :=
  (List.range (2 ^ S.firstBits)).filter fun i => !isPadding S i

/-- The number of the keys that are not padding: the length of the first vector. -/
def keyCount (S : Lkp.Public) : Nat := (realPlaces S).length

/-- The number of bits of the multiplicities: the length of the second vector. The third has
Lkp.allMasks S entries. -/
def planeBits (S : Lkp.Public) : Nat := 2 ^ (S.mu + S.d)

/-- The plan's entries of the lookup's rounds, with one number of bits of work in every round that
draws (Lkp.roundsOf). The block's run reads an entry's name and its numbers drawE, drawNZ, poss,
trits and rows; it does not read the work. -/
def entries (S : Lkp.Public) (work : Nat := 0) : List Fmt.Entry := (Lkp.roundsOf work S).map (·.entry)

/-- The statement from which the lookup starts. One main code serves the keys and the bits: a row
has 2^c places, c the smaller of the two numbers of index bits, and the longer vector has several
rows. Entry j of a vector is entry j of its table read as a vector. The lengths of the code words
and of the random tails are made up; the block reads neither. The main rows are over the extension
field, since the plain data's keys and bits may be any elements. -/
def statement (S : Lkp.Public) : Statement :=
  let c := min S.firstBits (S.mu + S.d)
  { codes := { base := #[⟨12, 2 ^ c, 4⟩], mask := #[⟨12, 2 ^ ceilLog2 (Lkp.allMasks S), 4⟩] }
    oracles := #[
      { shape := { code := 0, mainRows := 2 ^ (S.firstBits - c), mainDeg := 3 }, sampled := true,
        groups := [theGroup] },
      { shape := { code := 0, mainRows := 2 ^ (S.mu + S.d - c), mainDeg := 3 }, sampled := true,
        groups := [theGroup] },
      { shape := { maskRows := 1 }, sampled := true, groups := [theGroup],
        ledger := some { next := 0, left := Lkp.allMasks S, rows := 1, logRows := 0 } }]
    groups := #[{ code := 0, members := #[keysMessage, planesMessage, masksMessage],
                  kept := #[false, false, false] }] }

/-- What the block starts from. -/
def start (S : Lkp.Public) (work : Nat := 0) : Start where
  entries := entries S work
  st := statement S

/-! ## From plain data to the view -/

/-- A round fits its entry: as many elements are sent as the entry's bytes hold and as many are
drawn as it says; the drawn words are below p; the elements that must not be 0, which are drawn
last, are not. Nothing is asked of the size of the sent words. -/
def FlatRound.fits (r : FlatRound) (e : Fmt.Entry) : Bool :=
  24 * r.sent.length == e.msg && r.drawn.length == e.drawE &&
  r.drawn.all okE &&
  (r.drawn.drop (e.drawE - e.drawNZ)).all fun x => !isZeroE x

/-- The three vectors have their lengths, and all their words are below p. -/
def Flat.vectorsFit (t : Flat) (S : Lkp.Public) : Bool :=
  t.keys.length == keyCount S && t.planes.length == planeBits S &&
  t.masks.length == Lkp.allMasks S &&
  t.keys.all okE && t.planes.all okE && t.masks.all okE

/-- The plain data fit the lookup: there are as many rounds as entries, every round fits its entry,
and the three vectors fit. -/
def Flat.fits (t : Flat) (S : Lkp.Public) : Bool :=
  t.rounds.length == (entries S).length &&
  ((t.rounds.zip (entries S)).all fun p => p.1.fits p.2) && t.vectorsFit S

/-- A round as a view holds it. -/
def FlatRound.rv (r : FlatRound) : Fmt.RoundView where
  vals := r.sent.map fun x => Fmt.ItemValue.e x.triple
  drawn := ⟨r.drawn.map E.triple, [], [], none⟩

/-- An item as read, if it is an element of the extension field. -/
def elementOfGot : Fmt.ItemValue → Option E
  | .e x => some (E.ofTriple x)
  | _ => none

/-- Back: a view's round in which only elements are read and only elements are drawn. -/
def FlatRound.ofRV (r : Fmt.RoundView) : Option FlatRound :=
  if r.drawn.poss.isEmpty && r.drawn.trits.isEmpty && r.drawn.digest.isNone then
    (r.vals.mapM elementOfGot).map fun sent => ⟨sent, r.drawn.elems.map E.ofTriple⟩
  else none

/-- The view: the rounds; no column is opened. -/
def Flat.view (t : Flat) : Fmt.View where
  rounds := t.rounds.map FlatRound.rv
  opened := []

/-! ## The program's run -/

/-- The row that the caller makes of a claim on the keys. -/
def keysRow (k : Lkp.Keys) : Row :=
  (({ target := k.target } : Row).addForm keysMessage k.weights).addMasks k.masks

/-- The caller's block: the lookup, then a row of each claim on the keys. Returns what the lookup
returns and all rows of the group, in the order in which they were added. -/
def block (S : Lkp.Public) : Blk (Lkp.Out × Array Row) := do
  let o ← Lkp.verify S (fun row v => row.add planesMessage .main v) masksMessage theGroup
  o.keys.forM fun k => Blk.addRow theGroup (keysRow k)
  pure (o, (← Blk.group theGroup).rows)

/-- The program's run on the plain data. -/
def portOn (S : Lkp.Public) (t : Flat) (work : Nat := 0) : Except Failure (Lkp.Out × Array Row) :=
  (block S).runOn (start S work) t.view

/-! ## What is handed on, as plain data -/

/-- A row as plain data: the sum of the coefficients times the entries of the three vectors equals
the target. Each list goes with the list of the same name in Flat, entry by entry. -/
structure EndClaim where
  /-- the coefficients on the keys that are not padding -/
  keys : List E
  /-- the coefficients on the bits of the multiplicities -/
  planes : List E
  /-- the coefficients on the mask entries -/
  masks : List E
  /-- the target -/
  target : E
  deriving DecidableEq, Repr, Inhabited

/-- The row reads nothing but the caller's three vectors: its structured vectors are on the bits,
its single entries are mask entries that the lookup can take, its forms are on the keys, it has no
run, and its coefficient on every place of padding is 0. -/
def onCaller (S : Lkp.Public) (r : Row) : Bool :=
  r.runs.isEmpty &&
  (r.terms.all fun t => t.oracle == planesMessage && t.part == .main) &&
  (r.units.all fun u =>
    u.oracle == masksMessage && u.part == .mask && decide (u.index < Lkp.allMasks S)) &&
  (r.forms.all fun f => f.oracle == keysMessage) &&
  (List.range (2 ^ S.firstBits)).all fun i =>
    !isPadding S i || isZeroE (r.coefficient keysMessage .main i)

/-- A row, coefficient by coefficient. -/
def ofRow (S : Lkp.Public) (r : Row) : EndClaim where
  keys := (realPlaces S).map fun i => r.coefficient keysMessage .main i
  planes := (List.range (planeBits S)).map fun i => r.coefficient planesMessage .main i
  masks := (List.range (Lkp.allMasks S)).map fun i => r.coefficient masksMessage .mask i
  target := r.target

/-- What the program's verifier hands on at the plain data: the rows in the order in which they were
added, the row on the keys last. Nothing if the caller does not serve the lookup, the data do not
fit it, the run fails, or a row reads something else than the three vectors. -/
def endClaims (S : Lkp.Public) (t : Flat) : Option (List EndClaim) :=
  if served S && t.fits S then
    match portOn S t with
    | .ok (_, rows) => if rows.all (onCaller S) then some (rows.toList.map (ofRow S)) else none
    | .error _ => none
  else none

/-- The number of end claims of a lookup: a row for each sumcheck, the row on the bits at the last
sumcheck's point, the row on the sum of the counts, and a claim on each part's keys. -/
def claimCount (S : Lkp.Public) : Nat :=
  ((entries S).filter fun e => e.name == "PSC epsilon").length + 2 + S.parts.length

/-- The claim's three lists have the lengths of the lookup's three vectors, and all words are below
p, so that == on a target is the field's equality. -/
def EndClaim.fits (c : EndClaim) (S : Lkp.Public) : Bool :=
  c.keys.length == keyCount S && c.planes.length == planeBits S &&
  c.masks.length == Lkp.allMasks S &&
  c.keys.all okE && c.planes.all okE && c.masks.all okE && okE c.target

/-- The claim holds at the three vectors. Meant for a claim and vectors that fit: a sum goes as far
as the shorter of its two lists. `judge` tests that they fit. -/
def EndClaim.holds (c : EndClaim) (t : Flat) : Bool :=
  addE (addE (Psc.dot c.keys t.keys) (Psc.dot c.planes t.planes)) (Psc.dot c.masks t.masks) ==
    c.target

/-- What the evaluation of forms at the three vectors says. -/
inductive Verdict where
  /-- nothing was evaluated: the lookup is not served, the vectors or a form do not fit it, there
  are not as many forms as the lookup has end claims, or (portVerdict) the program handed none on -/
  | unfit
  /-- every form meets its target -/
  | holds
  /-- the number, from 1, of the first form that does not meet its target -/
  | fails (first : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The one evaluation. forms: forms with targets, as many as the lookup has end claims, whoever
made them. Of t only the three vectors are read. -/
def judge (S : Lkp.Public) (forms : List EndClaim) (t : Flat) : Verdict :=
  if served S && t.vectorsFit S && forms.length == claimCount S && forms.all (·.fits S) then
    match forms.findIdx? fun c => !c.holds t with
    | some i => .fails (i + 1)
    | none => .holds
  else .unfit

/-- The numbers, from 1, of all forms that do not meet their targets. Meant for forms and vectors at
which `judge` does not say unfit. -/
def failing (forms : List EndClaim) (t : Flat) : List Nat :=
  (((List.range forms.length).zip forms).filter fun p => !p.2.holds t).map (·.1 + 1)

/-- The evaluation of the program's own end claims at the plain data. -/
def portVerdict (S : Lkp.Public) (t : Flat) : Verdict :=
  match endClaims S t with
  | some l => judge S l t
  | none => .unfit

/-- The decision on plain data: the lookup is served, the data fit, the program's run goes through,
every row that it hands on reads the three vectors alone, the claims are as many as `claimCount`
says and fit, and every one holds at the three vectors (`endClaims`, `judge`). -/
def accepts (S : Lkp.Public) (t : Flat) : Bool := portVerdict S t == .holds

end OnBytes.G4
