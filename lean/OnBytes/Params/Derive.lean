-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Derive.lean: from the lines of the parameter file to what has no line.

The parameter file fixes what is free: the target, the bits of work, the shapes of the codes and
the stages of each proximity test. What follows from these has no line: the distance of a group,
its number of positions, the random entries of its codes, the later stages' mask messages. The C++
programs derive it (blocks/frame/derive.h, link_frame.h, files.h), and this file renders their
derivation for the committed table and for an entry file's one chain.

`entryParams` forms all of that chain's parameter bytes. The program does not call it or
`entrySized`: it forms its bytes in `configure` (OnBytes/Params/Configure.lean), which also asks the
tests on the finished shapes. Where `configure` returns a value, they are the same bytes: that is
proved (`configure_entry`, OnBytes/Params/ConfigureLaws.lean). Tests and files of theorems use the
two.

Main definitions: `placeCode`, `ioppStages`, `shapeOf`, `deriveTable`, `LinkSized`, `linkSized`,
`linkPlan`, `entrySized`, `entryParams`.
What is not claimed: no theorem is stated here. The tests by which the C++ refuses public files
whose finished shapes do not fit themselves or the codes are not asked in this file. They are asked
in OnBytes/Params/Configure.lean. Nor does `linkPlan` compare the solved stages, from which it
prices the proximity test, with the shape's stages under the chain's codes. The C++ ends the process
if they differ (iopp_sized_fault, blocks/iop/iopp.h). Here `linkSized` makes both from the same
values.
-/
import OnBytes.Iop.Link
import OnBytes.Params.Planner
import OnBytes.Params.Spell

namespace OnBytes.Params

/-- The number of a code in a list. A code that is not yet in the list is added to it. -/
def placeCode (list : Array Code) (c : CodeSize) : Array Code × Nat :=
  let code : Code := ⟨c.logN, c.ell, c.r⟩
  match list.toList.findIdx? (· == code) with
  | some i => (list, i)
  | none => (list.push code, list.size)

/-- From solved stages to the stages as a shape names them: each says its two codes by their numbers
in the lists `codes`, to which a code that is not yet there is added. -/
def ioppStages : List StageSize → Codes → List IoppStage × Codes
  | [], codes => ([], codes)
  | s :: rest, codes =>
    let a := placeCode codes.base s.g.main
    let z := placeCode codes.mask s.g.mask
    let x := ioppStages rest ⟨a.1, z.1⟩
    (⟨a.2, z.2, s.g.k, s.g.h⟩ :: x.1, x.2)

/-- The group of a line `group`, with 2 ^ k main rows and one mask row, before it is sized. -/
def shapeOf (l : GroupLine) (k : Nat) (overE : Bool) : GroupSize where
  main := { logN := l.logN, ell := 2 ^ l.logL, overE := overE }
  mask := { logN := l.maskLogN, ell := 2 ^ l.maskLogL, overE := true }
  k := k
  h := 0

/-- A group, the number of positions at which it is tested, and the stages of the proximity test on
it. The first stage is the group. -/
structure TestSizes where
  group : GroupSize
  t : Nat
  stages : List StageSize

/-- Solves a group and then the stages of the test on it. `draws t`: at how many drawn positions a
main row is opened in all when one list has t positions. -/
def solveTest (s : Setting) (scope : Scope) (l : GroupLine) (load : GroupLoad)
    (draws : Nat → Nat) (shape : GroupSize) : Option TestSizes := do
  let x ← solveGroup s scope load draws shape
  let st ← solveStages s scope x.group x.t l.stages
  pure ⟨x.group, x.t, st⟩

/-- The committed table at its distances. A record is a sample of the table's own, with `answers`
answers for each row (line `record`). The distances are derived (`sizeRecordedTable`): none if no
distance serves. Also none if data and random entries exceed the code's length. -/
def deriveTable (s : Setting) (l : Lines) : Option TableSize :=
  let T : TableSize :=
    { code := { logN := l.tableLogN, ell := l.tableData, r := l.tableRandom }
      v := l.tableRowsLog
      answers := l.answers }
  if T.code.n < T.code.dim then none
  else sizeRecordedTable s T l.slots l.blockLog

/-- The number of rows of an oracle message that holds `entries` entries in rows of `ell`. With
`rowsHigh` false it is rounded up to a power of two. -/
def linRowsOf (entries ell : Nat) (rowsHigh : Bool) : Nat :=
  let rows := (entries + ell - 1) / ell
  if rowsHigh then rows else pow2AtLeast rows

/-- The entries that a table's folded row takes in its oracle message: a row's data, a gap, and its
random entries, which begin at a multiple of a power of two (`FoldeqShape.entries`,
OnBytes/Iop/Foldeq.lean). The number depends only on the table's shape. -/
def foldedEntries (I : IndexShape) : Nat :=
  ({ index := I, u := {}, rowsHigh := true, leafClass := 0, columns := 0 } : FoldeqShape).entries

/-- The shape of a stored table as the items of a chain's parameter bytes write it. -/
def indexShapeOf (s : Setting) (T : TableSize) : IndexShape where
  code := ⟨T.code.logN, T.code.ell, T.code.r⟩
  v := T.v
  answers := s.samples
  saltBytes := s.saltBytes

/-- What follows from the lines for a link between two tables. -/
structure LinkSized where
  shape : LinkShape
  table : TableSize
  linked : TestSizes

/-- Sizes a link between the first table and a further copy. A link is one of the committer's files
and has the group of the one-time test's folded row (line `group once-folded`). The columns of the
first table are drawn at its distance as in a batch, those of the further table at the distance of a
one-time test, since nothing has been proved of that table before. `codes` is the list of the
chain's codes, to which the link's codes are added. The test that the finished shape fits itself and
the codes (link_fault) is asked in OnBytes/Params/Configure.lean. -/
def linkSized (s : Setting) (l : Lines) (T : TableSize) (codes : Codes) :
    Option (LinkSized × Codes) := do
  let A := tableAnalysis s T
  if !tableAdmitted T A then none
  let first := scopePositions s .once A.later.agree
  let further := scopePositions s .once A.once.agree
  if first == 0 || further == 0 then none
  let I := indexShapeOf s T
  if 40 < I.v || I.code.ell ≤ 3 * I.answers then none
  let rows := linRowsOf (foldedEntries I + s.samples) (2 ^ l.onceFolded.logL) true
  let group := shapeOf l.onceFolded (1 + clog2 rows) true
  let load : GroupLoad :=
    { cubeBits := stageCubeBits group, messages := 2,
      batchedRows := 2 * I.answers + first + further + 1 + 2 * s.samples }
  let x ← solveTest s .once l.onceFolded load id group
  match ioppStages x.stages codes with
  | (g :: later, codes') =>
    pure (⟨{ table := I, columnsFirst := first, columnsFurther := further, code := g.code,
             maskCode := g.maskCode, rows := rows, rowsHigh := true, leafClass := 0,
             masksAhead := true, later := later, choice := ⟨true⟩ }, T, x⟩, codes')
  | _ => none

/-- The rounds of a link's chain. -/
def linkPlan (x : LinkSized) : Planning Unit := do
  let s ← theSetting
  planRecord x.table
  let cube := clog2 x.shape.rows + clog2 x.linked.group.main.ell
  let nu ← planLink x.table ⟨cube, [x.linked.group]⟩
  needs (nu.1 == x.shape.columnsFirst && nu.2 == x.shape.columnsFurther)
  planIopp x.linked.stages (2 * x.shape.table.answers + nu.1 + nu.2 + 1 + 2 * s.samples)
    (if x.shape.masksAhead then 0 else 1) x.shape.choice.masksRide

/-- What follows for an entry file: the link's sizes, the codes of its chain and the chain's plan,
which holds. -/
def entrySized (l : Lines) : Except String (LinkSized × Codes × Planned) := do
  let s := settingOf l
  let T ← orRefuse (deriveTable s l)
  let (x, codes) ← orRefuse (linkSized s l T {})
  pure (x, codes, ← finishHeld s .once (linkPlan x))

/-- The parameter bytes of an entry file's chain, from the lines of the parameter file and the
digest of the public files. Refused if no admissible numbers follow from the lines, or if a round
of the plan does not hold at the target. The tests and conditions of OnBytes/Params/Configure.lean
are not asked here: public files that `configure` refuses can get bytes. -/
def entryParams (l : Lines) (cfg : ByteArray) : Except String ByteArray := do
  let (x, codes, p) ← entrySized l
  pure (Fmt.paramsBytes p.plan cfg [("codes", spellCodes codes), ("the link", spellLink x.shape)])

end OnBytes.Params
