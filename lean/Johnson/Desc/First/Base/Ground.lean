-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Base/Ground.lean: the changes to the statement and to the book of trees that the
steps of a description call, as plain functions on data.

This file holds definitions only; no theorem is stated.

Each of the sections 1 to 12 below follows a call of the program (OnBytes/Iop/Ground.lean, and
Send.admit of OnBytes/Iop/Send.lean) and writes it again as a test and an effect on the state DState
(DescState.lean): a new group; the oracle messages of one prover's message; a sample's answers; a
message joins a group; new open rows, one or several; the next free mask entries; a ledger is shut;
a message that is not sampled becomes a mask; a proximity test begins; messages whose trees another
chain has sent come in; a message is sampled in another statement.

The tests. A test is a list of named clauses (the names that end in L), written after the program's
call, clause by clause. Each clause bears the line of the program's text that it follows: a line of
OnBytes/Iop/Ground.lean unless another file is named. The function (the names that end in P) returns
nothing unless all clauses hold (ok). In this file's lists a clause on a value that is missing, such
as a message that is not there, counts as failed (has); a clause "… is there" on the same value
stands in front of it. on, which counts such a clause as held, is used by no list of this file: it
is for a list elsewhere that reads a value which may lawfully be missing, and that list says so at
the clause. A new list uses has. In elsewhereL the two clauses "the same main code" and "the same
mask code" ask that the code here is there and that the code there is that very code; the program's
call compares the two look-ups, which also agree where both codes are missing. groupL and sentL hold
the clauses that read the codes alone, so that a test on a plan, where there is no statement yet,
can call them; groupOk is groupL's three clauses as one test.

What the tests call. No function of the program's that says yes or no, or that may return nothing,
is called by name. Where the program's call asks such a function, the clause calls the description's
own text of it, at the same arguments: sentShapeFits (Johnson/Desc/Own/Sent.lean); placeFits,
coeffsInside, allZero (Own/Rows.lean); tensorInOrder, formFits (Own/Shapes.lean). Where it calls a
maker that may return nothing, that maker's text is called as it is taken over under a name as a
part of the description: treesCan, treesMade (Own/Trees.lean); padMade (Own/Send.lean); layoutOf
(Own/Layout.lean), which always returns. That each says or returns just what the program's does, at
all arguments, is stated in theorems beside these files (the files whose names end in Agree), which
Lean accepts and which this file does not import. Still called by name, each returning a number, an
element or a row, and always returning: Statement.tableBits, Row.coefficient, Row.renamed,
Blk.nextRealRow.

The effects. Nine are pure definitions of the library, called by name: stSent, treesSent, partsLaid
(OnBytes/Slice/BlkSendRun.lean); admitted, withMessageInGroup, withRow (OnBytes/Slice/BlkCalls.lean);
closeLedgers, runRows, begun (OnBytes/Slice/BlkBegin.lean). Written here: withGroup, the ledger's
step in takeMaskP, the mark in spendAsMaskP, and what adoptP and elsewhereP lay. withGroup has the
text of OnBytes.Slice.withGroup (OnBytes/Slice/BlkStLaws.lean); that file imports Mathlib and this
one does not, so it is written a second time. No theorem of this file ties the two.

One guard of the program is the caller's. Blk.addRowsOnView takes a function that may return
nothing, and refuses then; addRowsP takes the list itself. So whoever makes the list asks, at its
own line, that the rows can be made.

What is not claimed. That a test or an effect written here is that of the program's call: no theorem
of this file ties a function to the program. What linAdopt asks beside its two calls
(OnBytes/Iop/Lin.lean) is not here. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Base.DescState
import OnBytes.Slice.BlkCalls
import OnBytes.Slice.BlkSendRun
import Johnson.Desc.Own.Shapes
import Johnson.Desc.Own.Rows
import Johnson.Desc.Own.Sent
import Johnson.Desc.Own.Trees
import Johnson.Desc.Own.Layout
import Johnson.Desc.Own.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

variable {L : Type}

/-- A test: named clauses. -/
abbrev Clauses : Type := List (String × Bool)

/-- All clauses hold. -/
def ok (l : Clauses) : Bool := l.all (·.2)

/-- A clause on a value that may be missing: held where it is missing. A list that uses it asks
"… is there" of the same value in front, unless the value may lawfully be missing. -/
def on {α : Type} (x : Option α) (f : α → Bool) : Bool := (x.map f).getD true

/-- A clause on a value that must be there: FAILED where it is missing. -/
def has {α : Type} (x : Option α) (f : α → Bool) : Bool := (x.map f).getD false

/-! ## 1. A new group (Blk.newGroup, :1269-1275) -/

/-- Both codes are there, and the mask code is not longer than the main code: the three clauses of
newGroupL as one test on the codes alone, for a test on a plan.
-/
def groupOk (codes : Codes) (code maskCode : Nat) : Bool :=
  match codes.base[code]?, codes.mask[maskCode]? with
  | some c, some z => decide (z.logN ≤ c.logN)
  | _, _ => false

/-- The test of a new group reads the codes alone: so a test on a plan, where there is no statement
yet, can ask it. -/
def groupL (codes : Codes) (code maskCode : Nat) : Clauses :=
  [("newGroup: the main code is there", (codes.base[code]?).isSome),                    -- :1271
   ("newGroup: the mask code is there", (codes.mask[maskCode]?).isSome),                -- :1272
   ("newGroup: the mask code is not longer than the main",                              -- :1273
     has codes.base[code]? fun c => has codes.mask[maskCode]? fun z => decide (z.logN ≤ c.logN))]

def newGroupL (S : Statement) (code maskCode : Nat) : Clauses := groupL S.codes code maskCode

/-- The statement with one more group, which has no member and no row. -/
def withGroup (S : Statement) (code maskCode : Nat) : Statement :=
  { S with groups := S.groups.push { code := code, maskCode := maskCode } }

/-- One more group. Returns its number. -/
def newGroupP (d : DState L) (code maskCode : Nat) : Option (Nat × DState L) :=
  if ok (newGroupL d.st code maskCode) then
    some (d.st.groups.size, { d with st := withGroup d.st code maskCode })
  else none

/-! ## 2. The oracle messages of one prover's message (Blk.receiveOracles, :1473-1495) -/

/-- The two clauses on a prover's message that read the codes alone: for a test on a plan too. -/
def sentL (codes : Codes) (sent : Array OracleNotice) : Clauses :=
  [("recv: every notice's shape fits the codes",                                 -- :1477
    sent.all fun n => Own.sentShapeFits codes n.shape),
   ("recv: the trees can be laid", Own.treesCan codes sent)]                       -- :1479

def recvL (S : Statement) (B : TreeBook) (sent : Array OracleNotice) : Clauses :=
  sentL S.codes sent ++
  [("recv: statement and book are in step", S.oracles.size == B.place.size)]            -- :1478

/-- firstTree: the number of the first tree that the chain sends. Returns the messages' numbers. -/
def recvP (firstTree : Nat) (d : DState L) (sent : Array OracleNotice) :
    Option (Array Nat × DState L) :=
  if ok (recvL d.st d.book sent) then
    (Own.treesMade d.st.codes sent).map fun lay =>
      let n0 := d.st.oracles.size
      let base := d.book.trees.size
      ((Array.range sent.size).map (· + n0),
        { d with
          st := stSent d.st sent
          book :=
            { trees := partsLaid sent lay n0 base
                (treesSent firstTree lay.shapes.toList d.roots d.book.trees)
              place := d.book.place ++ (Array.range sent.size).map fun i =>
                (base + lay.tree.getD i 0, lay.part.getD i 0) }
          roots := d.roots + lay.shapes.size })
  else none

/-! ## 3. A sample's answers are in (Send.admit, OnBytes/Iop/Send.lean:167-179) -/

def admitL (S : Statement) (o : Nat) (rows : Array Row) : Clauses :=
  let x := S.oracles[o]?
  [("admit: the message is there", x.isSome),                            -- Send.lean:169; :1251
   ("admit: the pad's places exist",                                    -- Send.lean:171
    has x fun x => (Own.padMade S.codes x.shape).isSome),
   ("admit: not sampled before", has x fun x => !x.sampled),                     -- Send.lean:172
   ("admit: as many rows as answers", has x fun x => rows.size == x.shape.answers), -- Send.lean:172
   ("admit: an answer", has x fun x => decide (1 ≤ x.shape.answers))]            -- Send.lean:172

def admitP (d : DState L) (o : Nat) (rows : Array Row) : Option (DState L) :=
  if ok (admitL d.st o rows) then do
    let x ← d.st.oracles[o]?
    let places ← Own.padMade d.st.codes x.shape
    some { d with st := admitted d.st o x.shape places rows }
  else none

/-! ## 4. A message joins a group (Blk.join, :1288-1299) -/

def joinL (S : Statement) (g o : Nat) (kept : Bool) : Clauses :=
  let G := S.groups[g]?
  let x := S.oracles[o]?
  [("join: the group is there", G.isSome),                                       -- :1289; :1254
   ("join: the message is there", x.isSome),                                     -- :1290; :1251
   ("join: sampled", has x (·.sampled)),                                          -- :1291
   ("join: no test has begun", has G (!·.inRun)),                                 -- :1291
   ("join: the group's main code",                                               -- :1292
     has G fun G => has x fun x => x.shape.mainRows == 0 || x.shape.code == G.code),
   ("join: the group's mask code",                                               -- :1293
     has G fun G => has x fun x => x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode),
   ("join: no member twice", has G (!·.members.contains o)),                      -- :1294
   ("join: kept only with main rows",                                             -- :1295
    has x fun x => !kept || decide (0 < x.shape.mainRows))]

def joinP (d : DState L) (g o : Nat) (kept : Bool) : Option (DState L) :=
  if ok (joinL d.st g o kept) then
    (d.st.groups[g]?).map fun G => { d with st := withMessageInGroup d.st g o kept G }
  else none

/-! ## 5. and 6. New open rows (Blk.addRow, :1344-1360; Blk.addRowsOnView, :1363-1367) -/

def rowL (S : Statement) (g : Nat) (row : Row) : Clauses :=
  let G := S.groups[g]?
  [("addRow: the group is there", G.isSome),                                     -- :1346; :1254
   ("addRow: no test has begun", has G (!·.inRun)),                               -- :1347
   ("addRow: no sample row", row.kind != .sample),                               -- :1347
   ("addRow: the terms fit their places", has G fun G =>                          -- :1349
     row.terms.all fun t => Own.tensorInOrder t.v && Own.placeFits S G t.oracle t.part t.v.vars 0),
   ("addRow: the single entries fit their places", has G fun G =>                 -- :1350
     row.units.all fun u =>
       Own.placeFits S G u.oracle u.part (S.tableBits u.oracle u.part) u.index),
   ("addRow: the runs fit their places", has G fun G =>                           -- :1351-1354
     row.runs.all fun w =>
       Own.coeffsInside w.coeffs && decide (0 < w.coeffs.size) && decide (1 ≤ w.step) &&
         Own.placeFits S G w.oracle w.part (S.tableBits w.oracle w.part)
           (w.first + w.step * (w.coeffs.size - 1))),
   ("addRow: the forms fit their places", has G fun G =>                          -- :1355-1357
     row.forms.all fun f =>
       Own.placeFits S G f.oracle .main (S.tableBits f.oracle .main) 0 &&
         Own.formFits f.c (S.tableBits f.oracle .main)),
   ("addRow: ON VALUES: no coefficient on a pad", has G fun G =>                  -- :1358-1359
     G.members.all fun o =>
       ((S.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
         Own.allZero (row.coefficient o q.1 q.2))]

def addRowP (d : DState L) (g : Nat) (row : Row) : Option (DState L) :=
  if ok (rowL d.st g row) then some { d with st := withRow d.st g row } else none

def rowsL (S : Statement) (g : Nat) : Clauses :=
  [("addRows: the group is there", (S.groups[g]?).isSome),                       -- :1364; :1254
   ("addRows: no test has begun", has S.groups[g]? (!·.inRun))]                   -- :1365

/-- The rows one by one, in order. -/
def addRowsFrom (g : Nat) : List Row → DState L → Option (DState L)
  | [], d => some d
  | row :: l, d => (addRowP d g row).bind (addRowsFrom g l)

def addRowsP (d : DState L) (g : Nat) (rows : List Row) : Option (DState L) :=
  if ok (rowsL d.st g) then addRowsFrom g rows d else none

/-! ## 7. The next free mask entry (Blk.takeMask, :1309-1315; Blk.takeMasks, :1318-1326) -/

def takeMaskL (S : Statement) (o : Nat) : Clauses :=
  let x := S.oracles[o]?
  let l := x.bind (·.ledger)
  [("takeMask: the message is there", x.isSome),                                 -- :1310; :1251
   ("takeMask: it has a ledger", has x (·.ledger.isSome)),                        -- :1311
   ("takeMask: the ledger is not shut", has l (!·.closed)),                       -- :1312
   ("takeMask: an entry is left", has l fun l => decide (0 < l.left))]            -- :1312

/-- Returns the entry's index in o's mask table. -/
def takeMaskP (d : DState L) (o : Nat) : Option (Nat × DState L) :=
  if ok (takeMaskL d.st o) then
    ((d.st.oracles[o]?).bind (·.ledger)).map fun l =>
      let n := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next
      (n, { d with st := { d.st with oracles := d.st.oracles.modify o fun x =>
        { x with ledger := some { l with next := n + 1, left := l.left - 1 } } } })
  else none

/-- The next count free mask entries of o, appended to acc. -/
def takeMasksInto (o : Nat) : Nat → DState L → Array Nat → Option (List Nat × DState L)
  | 0, d, acc => some (acc.toList, d)
  | n + 1, d, acc =>
    match takeMaskP d o with
    | none => none
    | some (i, d') => takeMasksInto o n d' (acc.push i)

def takeMasksP (d : DState L) (o count : Nat) : Option (List Nat × DState L) :=
  takeMasksInto o count d #[]

/-! ## 8. A ledger is shut (Blk.closeLedger, :1329-1330, over Blk.onOracle, :1257-1260) -/

def closeLedgerL (S : Statement) (o : Nat) : Clauses :=
  [("closeLedger: the message is there", decide (o < S.oracles.size))]           -- :1258

def closeLedgerP (d : DState L) (o : Nat) : Option (DState L) :=
  if ok (closeLedgerL d.st o) then some { d with st := closeLedgers d.st [o] } else none

/-! ## 9. A message that is not sampled becomes a mask, once (Blk.spendAsMask, :1279-1282) -/

def spendAsMaskL (S : Statement) (o : Nat) : Clauses :=
  let x := S.oracles[o]?
  [("spendAsMask: the message is there", x.isSome),                              -- :1280; :1251
   ("spendAsMask: not sampled", has x (!·.sampled)),                              -- :1281
   ("spendAsMask: its shape counts no answer", has x (·.shape.answers == 0)),     -- :1281
   ("spendAsMask: not spent before", has x (!·.spentAsMask))]                     -- :1281

def spendAsMaskP (d : DState L) (o : Nat) : Option (DState L) :=
  if ok (spendAsMaskL d.st o) then
    some { d with st := { d.st with oracles := d.st.oracles.modify o fun x =>
      { x with spentAsMask := true } } }
  else none

/-! ## 10. A proximity test begins (Blk.beginRun, :1376-1386) -/

def beginRunL (S : Statement) (g : Nat) : Clauses :=
  let G := S.groups[g]?
  [("beginRun: the group is there", G.isSome),                                   -- :1377; :1254
   ("beginRun: no test has begun", has G (!·.inRun)),                             -- :1378
   ("beginRun: a member", has G (!·.members.isEmpty)),                            -- :1378
   ("beginRun: every member is there",                                           -- :1383; :1258
     has G fun G => G.members.all fun o => decide (o < S.oracles.size))]

/-- Returns the layout and the rows in the fixed order. -/
def beginRunP (d : DState L) (g : Nat) : Option (RunInput × DState L) :=
  if ok (beginRunL d.st g) then do
    let G ← d.st.groups[g]?
    some (⟨Own.layoutOf d.st G, runRows d.st G⟩, { d with st := begun d.st g G }) -- :1379; :1118
  else none

/-! ## 11. Messages whose trees another chain has sent come in (Blk.adoptOracles, :1661-1681) -/

def adoptL (S : Statement) (B : TreeBook) (sent : Array OracleNotice)
    (given : Array (Nat × Fmt.Src)) :
    Clauses :=
  [("adopt: every notice's shape fits the codes",                                -- :1665
    sent.all fun n => Own.sentShapeFits S.codes n.shape),
   ("adopt: every notice's shape counts an answer",                               -- :1665
    sent.all fun n => n.shape.answers != 0),
   ("adopt: statement and book are in step", S.oracles.size == B.place.size),           -- :1666
   ("adopt: the trees can be laid", Own.treesCan S.codes sent),                    -- :1667
   ("adopt: a number and a source for each tree",                                       -- :1668
     has (Own.treesMade S.codes sent) fun lay => lay.shapes.size == given.size)]

/-- given: for each tree that the messages make, its number and where a reader takes its root from.
No root is received. The messages come in as not yet sampled. Returns their numbers. -/
def adoptP (d : DState L) (sent : Array OracleNotice) (given : Array (Nat × Fmt.Src)) :
    Option (Array Nat × DState L) :=
  if ok (adoptL d.st d.book sent given) then
    (Own.treesMade d.st.codes sent).map fun lay =>
      let n0 := d.st.oracles.size
      let base := d.book.trees.size
      let laid := (List.range given.size).foldl (fun trees i =>
        let x := given.getD i (0, .own 0)
        trees.push { shape := lay.shapes.getD i {}, number := x.1, src := x.2 }) d.book.trees
      ((Array.range sent.size).map (· + n0),
        { d with
          st := stSent d.st sent
          book :=
            { trees := (List.range sent.size).foldl (fun trees i =>
                trees.modify (base + lay.tree.getD i 0) fun x =>
                  { x with parts := x.parts.push (n0 + i) }) laid
              place := d.book.place ++ (Array.range sent.size).map fun i =>
                (base + lay.tree.getD i 0, lay.part.getD i 0) } })
  else none

/-! ## 12. A message is sampled in another statement (Blk.sampledElsewhere, :1639-1651) -/

def elsewhereL (S : Statement) (mine : Nat) (other : Statement) (theirs : Nat) : Clauses :=
  let x := S.oracles[mine]?
  let y := other.oracles[theirs]?
  [("elsewhere: the message here is there", x.isSome),                            -- :1641; :1251
   ("elsewhere: the message there is there", y.isSome),                           -- :1642
   ("elsewhere: sampled there", has y (·.sampled)),                                -- :1645
   ("elsewhere: not sampled here", has x (!·.sampled)),                            -- :1645
   ("elsewhere: the same rows, degree and answers", has x fun x => has y fun y =>   -- :1646-1647
     x.shape.mainRows == y.shape.mainRows && x.shape.mainDeg == y.shape.mainDeg &&
       x.shape.maskRows == y.shape.maskRows && x.shape.answers == y.shape.answers),
   ("elsewhere: the same main code", has x fun x => has y fun y =>                  -- :1648
     x.shape.mainRows == 0 ||
       has S.codes.base[x.shape.code]? fun c => other.codes.base[y.shape.code]? == some c),
   ("elsewhere: the same mask code", has x fun x => has y fun y =>                  -- :1649
     x.shape.maskRows == 0 ||
       has S.codes.mask[x.shape.maskCode]? fun z => other.codes.mask[y.shape.maskCode]? == some z)]

/-- The sample rows are copied under the number here; the message gives no mask entries here. -/
def elsewhereP (d : DState L) (mine : Nat) (other : Statement) (theirs : Nat) : Option (DState L) :=
  if ok (elsewhereL d.st mine other theirs) then
    (other.oracles[theirs]?).map fun y =>
      { d with st := { d.st with oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine)
                 pad := y.pad } } }
  else none

end VerifiableInference.Desc.Ground
