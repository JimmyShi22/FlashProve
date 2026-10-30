-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Cs.lean: the code switch, on the verifier's side.
C++ counterpart: blocks/iop/cs.h (switch_rows, switch_verify, cs_sigma_verify, cs_verify).

Words (oracle message, group, open row, plan, strict reader): OnBytes/Iop/Ground.lean's sections.
From: single rows (OnBytes/Iop/Fold.lean): one main row and two mask rows, which are folds of rows
that were sent, perhaps kept rows (first section), and one linear claim on the messages they encode.
To: a new oracle message g under other codes, and linear claims on the message that g encodes and on
those of the oracle messages that take the kept rows. No later claim reads the old rows.

The idea. A row encodes a message together with a random tail. The message of g holds the messages
of the main row and the mask rows, and also the tails of all the old rows. So the symbol of an old
row at a position x is a public linear form of g's message: the row of the old code's generator
matrix at x. (For a kept row the form also reads the oracle message that takes the row.) The
verifier reads the old rows at t random positions. Each symbol read gives a claim "form = symbol".

The sections' headers say more. First: where things are in g, and kept rows. Second: the claims that
come out. Third: the messages, the two forms, and the order, which a caller of switchAdmit owes.

Main definitions: RowCut, SwitchTarget, switchTargetStage, SwitchPlaces, switchTargetCheck,
switchRows, switchVerify, csSigmaVerify, csVerify.

What this file does not do. No equation is tested here: every claim is deferred to the rows. (When
a row is added, Blk.addRow tests that it has the coefficient 0 on every pad; pads: first section.)
The strict reader, not this file, tests that the opened columns belong to their roots. The C++
programs also compare the codes of the old rows with the codes from which the plan's errors were
computed. Here the plan is an input and that comparison is not made. Why what is sent anew for a
kept member is what was sent before is argued in the head of blocks/iop/cs.h; that argument is not
stated or proved here. No theorem is stated here.
-/
import OnBytes.Iop.Send
import OnBytes.Iop.Bat
import OnBytes.Iop.Fold

namespace OnBytes

/-! ## Where the old rows' messages and tails are in the new oracle message

Where things are in g is data (SwitchTarget). Two vectors are placed in g's tables: the main row's
message, and "the rest": the messages of the mask rows, the tail of the main row, the tails of the
kept rows, the tails of the mask rows, the old pads of the kept oracle messages. (The pad of a
sample: the entries of a message that its sample rows read and no other row; OnBytes/Iop/Send.lean.)
A vector gets an aligned block of 2^bits rows of a table and fills it row index first. The rest is
placed in the entries of its block that are not in the pad of g's sample. Entries that a vector
leaves free in its block are part of g's message like any other (g's sample reads them), and no
claim of the switch reads them.

Kept rows. The old group may have members whose main rows FOLD has left as they were sent, because a
later part of the protocol reads them again. Each such member is sent a second time, in g's prover
message but as an oracle message of its own: under the new group's code, with a new tail and a
sample of its own. Its table is the old one except at the pad: the new pad takes the places of the
old pad, and the old pad's entries go into the rest, as do the old rows' tails. So a claim on the
old message, a kept row's generator row and the old sample row read the new oracle message
everywhere except at the pad's places; at those places they read the old pad in g. A generator row
also reads its row's old tail in g. -/

/-- An aligned block of 2^bits rows of one table, which takes a vector: entry j is in row firstRow +
(j mod 2^bits) at place j div 2^bits. firstRow is a multiple of 2^bits (switchTargetCheck). -/
structure RowCut where
  /-- which of the two tables -/
  part : Part := .main
  /-- the block has 2^bits rows -/
  bits : Nat := 0
  /-- the block's first row -/
  firstRow : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The oracle message that takes a kept member's rows. It has the same rows, field, message
length and number of answers as the old one. -/
structure KeptTarget where
  /-- its shape -/
  shape : OracleShape
  /-- its class of leaves -/
  leafClass : Nat := 0
  /-- in the new group its rows are kept rows once more -/
  keptAgain : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The target of a switch: the shape of g, where the two vectors are placed in it, and the oracle
messages that take the kept rows. -/
structure SwitchTarget where
  /-- the shape of g -/
  shape : OracleShape
  /-- the class of g's leaves -/
  leafClass : Nat := 0
  /-- takes the main row's message -/
  main : RowCut
  /-- takes the rest (SwitchParts) -/
  rest : RowCut
  /-- one for each kept member of the old group, in the order of sending -/
  kept : Array KeptTarget := #[]
  deriving DecidableEq, Repr, Inhabited

/-- The target inside a proximity test: 2^k main rows, which the main row's message fills, and 2^h
mask rows for the rest. It names no oracle message for kept rows, so a switch to it refuses single
rows whose layout has a kept member (switchTargetCheck). -/
def switchTargetStage (code maskCode k h answers : Nat) : SwitchTarget where
  shape := { code := code, mainRows := 2 ^ k, mainDeg := 3, maskCode := maskCode,
             maskRows := 2 ^ h, answers := answers }
  main := { part := .main, bits := k, firstRow := 0 }
  rest := { part := .mask, bits := h, firstRow := 0 }

/-- The number of bits that index the rows of a table of g: the table's row bits. -/
def switchRowBits (T : SwitchTarget) (part : Part) : Nat := ceilLog2 (T.shape.rows part)

/-- The number of places in a row of a table of g: the message length of the row's code. -/
def switchRowLength (codes : Codes) (T : SwitchTarget) : Part → Nat
  | .main => (codes.base.getD T.shape.code default).ell
  | .mask => (codes.mask.getD T.shape.maskCode default).ell

/-- The index in its table of entry j of a vector that a cut places: row + place 2^tableRowBits. -/
def cutIndex (cut : RowCut) (tableRowBits j : Nat) : Nat :=
  cut.firstRow + j % 2 ^ cut.bits + (j / 2 ^ cut.bits) * 2 ^ tableRowBits

/-- The kept members of the old group, in the order of sending. -/
def switchKept (old : SingleRows) : Array Nat :=
  ((old.layout.members.zip old.layout.kept).filter (·.2)).map (·.1)

/-- Where each part of the rest (see this section's header) begins within the rest, and how long
the rest is. The fields are in the order of the parts. -/
structure SwitchParts where
  /-- the message of each mask row -/
  maskAt : Array Nat := #[]
  /-- the tail of the main row -/
  mainTailAt : Nat := 0
  /-- the tail of each kept row, by member and row -/
  keptTailAt : Array Nat := #[]
  /-- the tail of each mask row -/
  maskTailAt : Array Nat := #[]
  /-- the old pad of each kept member -/
  oldPadAt : Array Nat := #[]
  /-- the length of the rest -/
  length : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The numbers start, start + step, start + 2 step, and so on: count numbers in all. -/
def startsFrom (start step count : Nat) : Array Nat :=
  (Array.range count).map fun j => start + step * j

/-- The pad of a sample, for a shape whose rows have room for it (switchTargetCheck tests this);
otherwise the empty list. -/
def padPlaces (codes : Codes) (s : OracleShape) : List PadPlace := (Send.pad codes s).getD []

/-- The pad of the sample of the oracle message number o. -/
def padOf (S : Statement) (o : Nat) : List PadPlace :=
  padPlaces S.codes (S.oracles.getD o default).shape

/-- The parts of the rest, in their order. -/
def switchParts (S : Statement) (old : SingleRows) : SwitchParts :=
  let code := S.codes.base.getD old.code default
  let zk := S.codes.mask.getD old.maskCode default
  let a := old.masks * zk.ell
  let b := a + code.r
  let c := b + old.keptRows * code.r
  let d := c + old.masks * zk.r
  let pads := (switchKept old).foldl
    (fun (s : Array Nat × Nat) o => (s.1.push s.2, s.2 + (padOf S o).length)) (#[], d)
  { maskAt := startsFrom 0 zk.ell old.masks
    mainTailAt := a
    keptTailAt := startsFrom b code.r old.keptRows
    maskTailAt := startsFrom c zk.r old.masks
    oldPadAt := pads.1
    length := pads.2 }

/-- The entries of g's table that take the rest, in order: those of the block that are not in the
pad of g's sample. The list can be as long as the block: SwitchPlaces.get computes an entry. -/
structure SwitchPlaces where
  /-- the block -/
  cut : RowCut
  /-- the row bits of the block's table -/
  rowBits : Nat
  /-- the pad's entries, numbered in the order in which the block is filled, increasing -/
  pad : List Nat
  /-- how many entries there are -/
  size : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The places of the rest in g. -/
def SwitchPlaces.make (codes : Codes) (T : SwitchTarget) : SwitchPlaces :=
  let cut := T.rest
  let rowBits := switchRowBits T cut.part
  let pad := (padPlaces codes T.shape).filterMap fun p =>
    let row := p.index % 2 ^ rowBits
    let place := p.index / 2 ^ rowBits
    if p.part == cut.part && cut.firstRow ≤ row && row < cut.firstRow + 2 ^ cut.bits then
      some (row - cut.firstRow + place * 2 ^ cut.bits)
    else none
  { cut := cut, rowBits := rowBits, pad := pad.mergeSort (· ≤ ·),
    size := switchRowLength codes T cut.part * 2 ^ cut.bits - pad.length }

/-- The index in g's table of entry i of the rest. It steps over the pad's entries that come
before. -/
def SwitchPlaces.get (P : SwitchPlaces) (i : Nat) : Nat :=
  cutIndex P.cut P.rowBits (P.pad.foldl (fun j p => if p ≤ j then j + 1 else j) i)

/-- True if the sizes in old, T and the statement, which are all public, fit a switch. -/
def switchTargetCheck (S : Statement) (old : SingleRows) (T : SwitchTarget) : Bool :=
  let codes := S.codes
  let s := T.shape
  let ell := (codes.base.getD old.code default).ell
  let mainBlock := 2 ^ T.main.bits
  let restBlock := 2 ^ T.rest.bits
  let kept := switchKept old
  old.masks == 2 &&
  decide (old.code < codes.base.size) && decide (old.maskCode < codes.mask.size) &&
  decide (s.code < codes.base.size) && decide (0 < s.mainRows) && s.mainDeg == 3 &&
  decide (1 ≤ s.answers) && (Send.pad codes s).isSome &&
  T.main.part == .main &&
  powerOfTwo ell &&
  T.main.firstRow % mainBlock == 0 && T.rest.firstRow % restBlock == 0 &&
  -- the two blocks are all the rows of g
  (match T.rest.part with
   | .mask =>
     decide (s.maskCode < codes.mask.size) && T.main.firstRow == 0 && mainBlock == s.mainRows &&
       T.rest.firstRow == 0 && restBlock == s.maskRows
   | .main =>
     s.maskRows == 0 && T.main.firstRow == 0 && T.rest.firstRow == mainBlock &&
       mainBlock + restBlock == s.mainRows) &&
  decide (mainBlock ≤ ell) && decide (ell ≤ (codes.base.getD s.code default).ell * mainBlock) &&
  decide ((switchParts S old).length ≤ (SwitchPlaces.make codes T).size) &&
  T.kept.size == kept.size &&
  (kept.zip T.kept).all fun p =>
    let o := (S.oracles.getD p.1 default).shape
    let n := p.2.shape
    o.maskRows == 0 && n.maskRows == 0 && decide (n.code < codes.base.size) &&
      (Send.pad codes o).isSome &&
      n.mainRows == o.mainRows && n.mainDeg == o.mainDeg && n.answers == o.answers &&
      (codes.base.getD n.code default).ell == (codes.base.getD o.code default).ell

/-! ## The claims on the new oracle message

The claims that come out, in this order: the old claim, moved to where its rows' messages are in
g; the old sample rows of each kept oracle message; for each draw, in the order drawn, the generator
rows of the main row, the kept rows, the old mask row and the fresh mask row. A position that is
drawn twice gives its rows twice. The statement keeps g's sample rows, one for each answer. -/

/-- A coefficient vector on the main row's message (2^vars entries), carried to g's main table.
The row bits above the block pick the block; places beyond the vector get no weight. -/
def switchLift (c : Form) (vars : Nat) (cut : RowCut) (tableRowBits tableBits : Nat) : Form :=
  let above := tableRowBits - cut.bits
  (c.insertChoice cut.bits above (cut.firstRow / 2 ^ cut.bits)).insertChoice (vars + above)
    (tableBits - (vars + above)) 0

/-- A piece of a stretch of the rest whose entries are equally spaced in g's table. -/
structure SwitchPiece where
  /-- the piece holds the entries start, .., stop - 1 of the stretch -/
  start : Nat
  /-- one more than the number, in the stretch, of the piece's last entry -/
  stop : Nat
  /-- the index in the table of the piece's first entry -/
  first : Nat
  /-- the distance in the table from one entry of the piece to the next -/
  step : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A piece to which switchPieces is still adding entries. -/
structure OpenPiece where
  /-- the number of its first entry in the stretch -/
  start : Nat
  /-- the index in the table of its first entry -/
  first : Nat
  /-- the step, once there is a second entry -/
  step : Option Nat
  /-- the index in the table of its last entry so far -/
  last : Nat

/-- The piece as it is when entry number stop does not belong to it any more. -/
def OpenPiece.close (p : OpenPiece) (stop : Nat) : SwitchPiece :=
  ⟨p.start, stop, p.first, p.step.getD 1⟩

/-- The entries first, .., first + count - 1 of the rest, cut into pieces that are equally spaced
in g's table. Each piece is as long as it can be: it ends where the spacing changes, as at a pad. -/
def switchPieces (places : SwitchPlaces) (first count : Nat) : List SwitchPiece :=
  let run := (List.range count).foldl
    (fun (s : List SwitchPiece × Option OpenPiece) i =>
      let p := places.get (first + i)
      match s.2 with
      | none => (s.1, some ⟨i, p, none, p⟩)
      | some o =>
        match o.step with
        | none => (s.1, some { o with step := some (p - o.first), last := p })
        | some d =>
          if p == o.last + d then (s.1, some { o with last := p })
          else (o.close i :: s.1, some ⟨i, p, none, p⟩))
    ([], none)
  match run.2 with
  | none => []
  | some o => (o.close count :: run.1).reverse

/-- Coefficients over E, written out, on a stretch of the rest: one run for each piece. -/
def switchAddRestE (row : Row) (g : Nat) (part : Part) (pieces : List SwitchPiece)
    (coeff : Array E) : Row :=
  pieces.foldl (fun r p => r.addRun g part p.first p.step (.own (coeff.extract p.start p.stop))) row

/-- Coefficients over F, as a generator row has them, on a stretch of the rest: one run for each
piece. The runs all read the one vector coeff; none gets a copy. -/
def switchAddRestF (row : Row) (g : Nat) (part : Part) (pieces : List SwitchPiece)
    (coeff : Array F) : Row :=
  pieces.foldl
    (fun r p => r.addRun g part p.first p.step (.stretch coeff p.start (p.stop - p.start))) row

/-- An aligned box in a table: 2^vars entries (vars is the caller's) at equal distances 2^shift from
an index whose bits shift, .., shift + vars - 1 are 0. A product form on them is one tensor. -/
structure SwitchBox where
  /-- the distance is 2^shift -/
  shift : Nat
  /-- the index of the first entry -/
  start : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The box that holds the entries first, .., first + 2^vars - 1 of the rest. Nothing if no box
holds them, if vars is 0, or if the rest's places end before the last of them. -/
def switchBox (places : SwitchPlaces) (first vars : Nat) : Option SwitchBox :=
  let count := 2 ^ vars
  if vars == 0 || places.size < first + count then none
  else
    let start := places.get first
    let step := places.get (first + 1) - start
    if !powerOfTwo step then none
    else if !((List.range count).all fun i => places.get (first + i) == start + i * step) then none
    else if start / step % count != 0 then none
    else some ⟨ceilLog2 step, start⟩

/-- A tensor on vars variables, the bits of an entry's number within the box, as a tensor on the
table. -/
def switchOnBox (b : SwitchBox) (v : Tensor) (vars tableBits : Nat) : Tensor :=
  (v.insertChoice 0 b.shift (b.start % 2 ^ b.shift)).insertChoice (b.shift + vars)
    (tableBits - b.shift - vars) (b.start / 2 ^ (b.shift + vars))

/-- A form on the main table of an old kept member, carried over. It goes to the same entries of
the new oracle message, except at the places of the pad. At those places the new message has its
own pad, and the form's coefficients go to where the old pad is in g. -/
def switchAddKept (row : Row) (pad : List PadPlace) (anew g : Nat) (restPart : Part)
    (places : SwitchPlaces) (oldPadAt : Nat) (c : Form) : Row :=
  (pad.zipIdx).foldl
    (fun r p =>
      let there := c.entry p.1.index
      (r.addUnit anew .main p.1.index (negE there)).addUnit g restPart
        (places.get (oldPadAt + p.2)) there)
    (row.addForm anew c)

/-- A row that reads the main table of the oracle message o and nothing else, as a form on that
table. Nothing if it reads something else. -/
def switchFormOn (o : Nat) (row : Row) : Option Form :=
  if (row.terms.all fun t => t.oracle == o && t.part == .main) &&
      (row.units.all fun u => u.oracle == o && u.part == .main) &&
      (row.runs.all fun r => r.oracle == o && r.part == .main) &&
      row.forms.all fun f => f.oracle == o then
    let a := row.terms.foldl (fun (c : Form) t => c.add t.v) {}
    let b := row.units.foldl (fun (c : Form) u => c.addEntry u.index u.coeff) a
    let d := row.runs.foldl
      (fun (c : Form) r =>
        (List.range r.coeffs.size).foldl
          (fun c j => c.addEntry (r.first + r.step * j) (r.coeffs.get j)) c) b
    some (row.forms.foldl (fun (c : Form) f => c.plus f.c) d)
  else none

/-- What a switch needs to know of one kept member of the old group. -/
structure KeptPlace where
  /-- the member's number -/
  old : Nat
  /-- the number of the oracle message that takes its rows -/
  anew : Nat
  /-- its main rows -/
  rows : Nat
  /-- the number of bits that index its main rows -/
  rowBits : Nat
  /-- the pad of its sample -/
  pad : List PadPlace
  /-- where its old pad begins in the rest -/
  oldPadAt : Nat

/-- What switchRows computes once for a switch and uses for every row. -/
structure SwitchFrame where
  /-- the number of g -/
  g : Nat
  /-- the table of g that takes the rest -/
  restPart : Part
  /-- the old main code -/
  code : Code
  /-- the old mask code -/
  zk : Code
  /-- the row bits of g's main table -/
  rowBits : Nat
  /-- all index bits of g's main table -/
  tableBits : Nat
  /-- all index bits of the table that takes the rest -/
  restBits : Nat
  /-- the block of the main row's message -/
  mainCut : RowCut
  /-- the places of the rest -/
  places : SwitchPlaces
  /-- where the parts of the rest begin -/
  parts : SwitchParts
  /-- the kept members, in the order of sending -/
  kept : List KeptPlace
  /-- the pieces of the main row's tail -/
  mainTail : List SwitchPiece
  /-- the pieces of each kept row's tail -/
  keptTail : Array (List SwitchPiece)
  /-- for each mask row: the box of its message, if there is one -/
  box : Array (Option SwitchBox)
  /-- for each mask row: the pieces of its message, if it has no box -/
  maskMessage : Array (List SwitchPiece)
  /-- for each mask row: the pieces of its tail -/
  maskTail : Array (List SwitchPiece)

/-- The frame of a switch. Nothing if a code is not there, or if there is not one new oracle message
for each kept member. A kept member that the statement lacks counts as a message without rows. -/
def switchFrame (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) : Option SwitchFrame := do
  let codes := S.codes
  let code ← codes.base[old.code]?
  let zk ← codes.mask[old.maskCode]?
  let newCode ← codes.base[T.shape.code]?
  let keptIds := switchKept old
  guard (anew.size == keptIds.size)
  let parts := switchParts S old
  let places := SwitchPlaces.make codes T
  let rowBits := switchRowBits T .main
  let cube := powerOfTwo zk.ell
  let box := (Array.range old.masks).map fun j =>
    if cube then switchBox places (parts.maskAt.getD j 0) (ceilLog2 zk.ell) else none
  pure {
    g := g, restPart := T.rest.part, code := code, zk := zk, rowBits := rowBits
    tableBits := rowBits + newCode.logEll
    restBits := S.tableBits g T.rest.part
    mainCut := T.main, places := places, parts := parts
    kept := (List.range keptIds.size).map fun i =>
      let o := keptIds.getD i noId
      { old := o, anew := anew.getD i noId, rows := (S.oracles.getD o default).shape.mainRows,
        rowBits := S.rowBits o .main, pad := padOf S o, oldPadAt := parts.oldPadAt.getD i 0 }
    mainTail := switchPieces places parts.mainTailAt code.r
    keptTail := parts.keptTailAt.map fun a => switchPieces places a code.r
    box := box
    maskMessage := (Array.range old.masks).map fun j =>
      if (box.getD j none).isSome then [] else switchPieces places (parts.maskAt.getD j 0) zk.ell
    maskTail := parts.maskTailAt.map fun a => switchPieces places a zk.r }

/-- A form on the main table of the kept member k, carried over (switchAddKept). -/
def SwitchFrame.addKept (W : SwitchFrame) (row : Row) (k : KeptPlace) (c : Form) : Row :=
  switchAddKept row k.pad k.anew W.g W.restPart W.places k.oldPadAt c

/-- The old claim, carried over. It is a row even if it reads nothing: "0 = target" is a claim.
Nothing if it reads a kept member that the group does not have. -/
def switchCarried (W : SwitchFrame) (old : SingleRows) : Option Row := do
  let a : Row := ({} : Row).addForm W.g
    (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits)
  let b ← old.kept.foldlM
    (fun (r : Row) f => do
      let k ← W.kept.find? (·.old == f.oracle)
      pure (W.addKept r k f.c)) a
  let c := (List.range old.masks).foldl
    (fun (r : Row) j =>
      let d := old.d.getD j #[]
      switchAddRestE r W.g W.restPart (switchPieces W.places (W.parts.maskAt.getD j 0) d.size) d) b
  pure { c with target := old.target }

/-- The old sample rows of the kept members, carried over (switchAddKept), each as a row of its own,
in the order of sending. What they are for is said in the head of blocks/iop/cs.h. Nothing if a
sample row reads anything other than its member's main table. -/
def switchOldSamples (S : Statement) (W : SwitchFrame) : Option (List Row) :=
  (W.kept.mapM fun (k : KeptPlace) =>
    (S.oracles.getD k.old default).sampleRows.toList.mapM fun (sample : Row) => do
      let c ← switchFormOn k.old sample
      pure ({ W.addKept {} k c with target := sample.target } : Row)).map List.flatten

/-- The generator rows of one draw x. symbols: the symbols read at x, in the order of the rows:
the main row, the kept rows, the mask rows. -/
def switchGenerators (W : SwitchFrame) (old : SingleRows) (x : Nat) (symbols : Nat → E) :
    List Row :=
  let atX := generatorAt W.code x
  let onMessage : Form :=
    Form.ofTensor (Tensor.product (atX.f.take W.code.logEll) (ofF atX.messageScale))
  let onTail := generatorTail W.code x
  let finish := fun (r : Row) (row : Nat) =>
    ({ r with kind := .generator, target := symbols row } : Row)
  let main :=
    finish (switchAddRestF
      (({} : Row).addForm W.g (switchLift onMessage W.code.logEll W.mainCut W.rowBits W.tableBits))
      W.g W.restPart W.mainTail onTail) 0
  -- the kept rows are under the main row's code and are read at x itself
  let kept := (W.kept.foldl
    (fun (s : List Row × Nat) (k : KeptPlace) =>
      (List.range k.rows).foldl
        (fun (s : List Row × Nat) b =>
          let r := W.addKept {} k (onMessage.insertChoice 0 k.rowBits b)
          (finish (switchAddRestF r W.g W.restPart (W.keptTail.getD s.2 []) onTail) (1 + s.2)
            :: s.1, s.2 + 1)) s)
    ([], 0)).1.reverse
  let xZk := shortPosition W.zk.logN x
  let atZk := generatorAt W.zk xZk
  let zkTail := generatorTail W.zk xZk
  let masks := (List.range old.masks).map fun j =>
    let onMask : Row :=
      match W.box.getD j none with
      | some b =>
        ({} : Row).add W.g W.restPart
          (switchOnBox b (Tensor.product (atZk.f.take (ceilLog2 W.zk.ell)) (ofF atZk.messageScale))
            (ceilLog2 W.zk.ell) W.restBits)
      | none =>
        switchAddRestF {} W.g W.restPart (W.maskMessage.getD j []) (generatorMessage W.zk xZk)
    finish (switchAddRestF onMask W.g W.restPart (W.maskTail.getD j []) zkTail) (old.maskRow j)
  main :: kept ++ masks

/-- The old claim, the kept members' old sample rows and the generator rows, as rows on g and on the
oracle messages anew that take the kept members' rows. y: the symbols read, by position in pos.all
(each position once), then by row. Nothing if y does not have one symbol for each row at each of
these, if a draw is not among them, or if switchFrame, switchCarried or switchOldSamples fails. -/
def switchRows (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (pos : Positions) (y : Array E) : Option (List Row) := do
  guard (y.size == pos.all.size * old.rows)
  let W ← switchFrame S old T g anew
  let carried ← switchCarried W old
  let samples ← switchOldSamples S W
  let gens ← pos.draws.toList.mapM fun x => do
    let i ← pos.indexOf x
    pure (switchGenerators W old x fun row => y.getD (i * old.rows + row) zeroE)
  pure (carried :: samples ++ gens.flatten)

/-- What a switch returns. -/
structure Switched where
  /-- the number of g -/
  g : Nat := noId
  /-- the oracle messages that take the kept members' rows -/
  kept : Array Nat := #[]
  /-- the other oracle messages that went in g's prover message -/
  others : Array Nat := #[]
  /-- where the old rows were read -/
  positions : Positions := {}
  deriving Inhabited

/-- g and the oracle messages that take kept rows join the group named by to, and the claims become
its open rows. The positions in out must have been drawn after SEND's answers (Order, in the next
section). Nothing here tests that: of the order, Blk.join sees only that a message was sampled.
In blocks/iop/cs.h only switch_verify and switch_prove can call switch_admit (key: SwitchAccess). -/
def switchAdmit (old : SingleRows) (T : SwitchTarget) (to : Nat) (out : Switched)
    (y : Array E) : Blk Unit := do
  -- g's mask rows hold what the switch carries: no entry is free for a mask
  if 0 < T.shape.maskRows then Blk.closeLedger out.g
  Blk.join to out.g
  for p in out.kept.zip T.kept do
    Blk.join to p.1 p.2.keptAgain
  let S ← Blk.statement
  Blk.addRowsOnView to fun _ => switchRows S old T out.g out.kept out.positions y

/-! ## The verifier

Messages.
 1. The prover sends g. Other oracle messages may follow in the same prover's message.
 2. The verifier sends the seeds of the out-of-domain sample, one for each answer.
 3. The prover sends the answers.
 4. The verifier draws positions of the old rows and, in the form csVerify, one element theta.
The prover opens the old rows at the positions.

Order. The positions come after the answers. The protocol's argument is that near the word that was
sent for g there may be several code words, and that a prover that knew the positions before it
answered could pick the one that fits them. switchVerify keeps this order: it runs SEND and then
draws the positions. theta shares the positions' message; the argument for that is that the rows
that it batches are fixed by what was sent before and by the positions.

The two forms. csSigmaVerify ends with the claims of the second section: they become open rows of
the group that the caller names.
csVerify adds one step: all rows of that group are batched with the powers of theta. That step is
BAT (OnBytes/Iop/Bat.lean), the first step of a proximity test on the group, with its element drawn
early. -/

/-- The switch from old to T; g joins the group named by to. others: further oracle messages of g's
prover's message. SEND leaves the round of its answers open, and the verifier's message with the
positions closes it. withTheta: that round is named CS and draws one element after the positions,
which is returned; otherwise it is named LOC and 0 is returned. Fails unless switchTargetCheck. -/
def switchVerify (old : SingleRows) (T : SwitchTarget) (to : Nat) (others : Array OracleNotice)
    (withTheta : Bool) : Blk (Switched × E) := do
  let S ← Blk.statement
  Blk.must (switchTargetCheck S old T)
  let notices := #[(⟨T.shape, T.leafClass⟩ : OracleNotice)] ++
    T.kept.map (fun k => ⟨k.shape, k.leafClass⟩) ++ others
  let ids ← sendVerify notices false
  let code ← Blk.get S.codes.base[old.code]?
  let drawn ← Blk.closePositions (if withTheta then "CS" else "LOC") code.logN
  let theta ←
    match withTheta, drawn.2 with
    | true, [x] => pure x
    | false, [] => pure zeroE
    | _, _ => Blk.fail
  let out : Switched :=
    { g := ids.getD 0 noId, kept := ids.extract 1 (1 + T.kept.size),
      others := ids.extract (1 + T.kept.size) ids.size, positions := drawn.1 }
  let y ← singleRowsRead old out.positions
  -- notes (Blk.noteBy), which no test reads: the folded symbols at the first draw
  let first := ((out.positions.draws[0]?).bind out.positions.indexOf).getD 0 * old.rows
  Blk.noteBy "CS: y_main at the first draw" fun _ => y.getD first zeroE
  Blk.noteBy "CS: y_0 at the first draw" fun _ => y.getD (first + old.maskRow 0) zeroE
  Blk.noteBy "CS: y_1 at the first draw" fun _ => y.getD (first + old.maskRow 1) zeroE
  switchAdmit old T to out y
  pure (out, theta)

/-- The code switch that leaves its claims as open rows of the group named by to. -/
def csSigmaVerify (old : SingleRows) (T : SwitchTarget) (to : Nat)
    (others : Array OracleNotice) : Blk Switched := do
  pure (← switchVerify old T to others false).1

/-- switchVerify, then BAT: all rows of the group named by to (its open rows and its members' sample
rows) are batched with the powers of the element drawn after the positions. From then on the group
takes no members or rows (Blk.beginRun). The number of rows must be that of the plan's entry for the
round (Blk.requireRows). Returns what the switch returns, the one row, and the group's layout. -/
def csVerify (old : SingleRows) (T : SwitchTarget) (to : Nat) (others : Array OracleNotice) :
    Blk (Switched × GroupRow × GroupLayout) := do
  let (out, theta) ← switchVerify old T to others true
  let run ← Blk.beginRun to
  Blk.requireRows run.rows.size
  let S ← Blk.statement
  let row ← Blk.getOnView { group := to } fun _ => Bat.combine S to run theta
  pure (out, row, run.layout)

end OnBytes
