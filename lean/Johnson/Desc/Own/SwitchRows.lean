-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/SwitchRows.lean: the rows that a code switch lays on the new group, in a
text of this library's description: the old claim carried over, the kept members' old sample rows
carried over, and the generator rows of each drawn position (`swRows`), with the four makers that
it calls: the switch's frame (`swFrame`), the carried claim (`swCarried`), the old sample rows
(`swOldSamples`) and a row read as a form on one table (`swFormOn`). Definitions with code; no monad
of the hand-written program but Option.

EVERY PLACE AT WHICH ONE OF THE FIVE RETURNS NOTHING, AND WHAT IS ASKED THERE. All are faults of
shape: none compares a value that a prover sends.
  `swFormOn o row`, one place: IS THE ROW A ROW ON ONE TABLE? Every summand of the row (tensor,
      single entry, run) reads the main table of the oracle message o, and every form among its
      summands is a form on o. Else nothing.
  `swFrame S old T g anew`, four places, in this order:
      (1) the number of the old main code (old.code) names a code in the statement's list of main
          codes;
      (2) the number of the old mask code (old.maskCode) names a code in the list of mask codes;
      (3) the number of g's main code (T.shape.code) names a code in the list of main codes;
      (4) there are as many new oracle messages (anew) as the old rows' layout has kept members.
      IT DOES NOT ASK that a kept member's number names a message of the statement: a member that
      the statement lacks counts as a message without rows.
  `swCarried W old`, one place: DOES THE CLAIM READ KEPT MEMBERS ALONE? Each form that the old claim
      has on a kept member's table (old.kept) names a message that is a kept member in the frame.
  `swOldSamples S W`, one place: each stored sample row of each kept member is a row on that
      member's main table alone (`swFormOn`).
  `swRows S old T g anew pos y`, five places, in this order:
      (1) y has one symbol for each of the old rows at each position of the list (pos.all);
      (2) `swFrame` returns; (3) `swCarried` returns; (4) `swOldSamples` returns;
      (5) each draw (pos.draws) stands in the list of positions.

What is called of the hand-written program (OnBytes/Iop/Cs.lean and what it imports): the records
with their fields (Statement, SingleRows, SwitchTarget, SwitchFrame, KeptPlace, Positions, Row,
Form); and functions that always return a value: switchKept, switchParts, SwitchPlaces.make,
switchRowBits, switchPieces, padOf, Statement.tableBits, Statement.rowBits, Code.logEll, ceilLog2,
switchLift, SwitchFrame.addKept, switchAddRestE, switchGenerators, SingleRows.rows, Row.addForm,
Coeffs.size, Coeffs.get and Form's add, addEntry, plus. By a walk over constants beneath the five,
three functions of that program that can say no are still reached, and no refusal hangs on any of
them: powerOfTwo and switchBox choose between two ways of writing a mask row's message (as a box,
or piece by piece); Send.pad stands beneath padOf, which takes a shape for which no pad can be made
as a shape with an empty pad.

HOW FAR THE TEXT IS ITS OWN. It is the hand-written program's text, token for token, but for the
five names and one reading: where that text says «pos.indexOf x» this one says «pos.all.idxOf? x»,
which is that function's whole body. It adds no second eye: a fault of the hand-written text is a
fault of this one. That each of the five agrees with the hand-written program's at all arguments is
proved in Johnson/Desc/Own/SwitchRowsAgree.lean, which no block imports.
Limits: no law on what the rows mean. Whether the places above ask enough is not said here.

-/
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- A row that reads the main table of the oracle message o and nothing else, as a form on that
table. Nothing if it reads something else. -/
def swFormOn (o : Nat) (row : Row) : Option Form :=
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

/-- The frame of a switch. Nothing if one of the three codes is not there, or if there is not one
new oracle message for each kept member. -/
def swFrame (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
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

/-- The old claim, carried over. It is a row even if it reads nothing: "0 = target" is a claim.
Nothing if it reads a kept member that the frame does not have. -/
def swCarried (W : SwitchFrame) (old : SingleRows) : Option Row := do
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

/-- The old sample rows of the kept members, carried over, each as a row of its own, in the order of
sending. Nothing if a sample row reads anything other than its member's main table. -/
def swOldSamples (S : Statement) (W : SwitchFrame) : Option (List Row) :=
  (W.kept.mapM fun (k : KeptPlace) =>
    (S.oracles.getD k.old default).sampleRows.toList.mapM fun (sample : Row) => do
      let c ← swFormOn k.old sample
      pure ({ W.addKept {} k c with target := sample.target } : Row)).map List.flatten

/-- **The rows of a code switch**: the old claim, the kept members' old sample rows and the
generator rows, as rows on g and on the oracle messages anew that take the kept members' rows. y:
the symbols read, by position in pos.all (each position once), then by row. -/
def swRows (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (pos : Positions) (y : Array E) : Option (List Row) := do
  guard (y.size == pos.all.size * old.rows)
  let W ← swFrame S old T g anew
  let carried ← swCarried W old
  let samples ← swOldSamples S W
  let gens ← pos.draws.toList.mapM fun x => do
    let i ← pos.all.idxOf? x
    pure (switchGenerators W old x fun row => y.getD (i * old.rows + row) zeroE)
  pure (carried :: samples ++ gens.flatten)

end VerifiableInference.Desc.Own
