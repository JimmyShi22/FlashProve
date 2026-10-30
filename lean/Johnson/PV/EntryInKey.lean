-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/EntryInKey.lean: beside Johnson/PV/EntryInOf.lean: the key's side of the entry's input,
and controls for tests.
`keyRecOf`, `keyRecS`, `keyRecD`: the key's root and record out of key.parsed.bin and its file of
seeds; an Except whose error says who refused; with the carrier's root and answers beside, and its
judged rows. `tieRows`: the two rows that want both files: the key's root has 32 bytes; the leaf
file's copy of the first table is the parsed key file's. `entryAllS`, `entryAllD`: all in one: the
root, the record, the entry's input and the rows in order; no error at a no: the rows are to be
judged by the caller.
`flipD`, `headBy`, `firstRow`: small helpers, twins of those in a file that is not in this library
(`flipD`, `headBy` and the body of `firstRow` to the letter). `tabControls`, `entryControlsS`,
`entryControlsD`, `controlsFitT`, `controlsFitS`, `controlsFitD`: three changed tables and their
condition. `seedTurned`: a fourth control, on a record.

-/
import Johnson.PV.EntryInOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.EntryInOf
open OnBytes OnBytes.Maker OnBytes.Slice
open _root_.Iop (Dig)
open _root_.Run (bytesToDig)
open Johnson.RunOne.StrictB (freePlace oneMore)

/-- What is laid of the parsed key file and its seeds' file. -/
structure KeyRec (v lg s : ℕ) where
  cm : Dig 256
  rcd : RecP NZ v lg s
  root : ByteArray
  answers : List (UInt64 × UInt64 × UInt64)
  front : List (String × Bool)

/-- **The key's root and record.** -/
def keyRecOf (v lg s : ℕ) (kb sb : ByteArray) : Except String (KeyRec v lg s) :=
  match Carrier.read Carrier.magicKey kb, Carrier.readSeeds sb with
  | .error w, _ => .error s!"keyRec: Carrier.read at key.parsed.bin refuses: {w}"
  | _, .error w => .error s!"keyRec: Carrier.readSeeds at key.parsed.bin.seeds refuses: {w}"
  | .ok k, .ok sd =>
    let t : OnBytes.Params.TableName := ⟨k.root, k.answers.map E.ofTriple⟩
    .ok
      { cm := bytesToDig k.root
        rcd := OnBytes.K.recOne v lg s t (sd.map fun y => (y.1.map E.ofTriple, E.ofTriple y.2))
        root := k.root, answers := k.answers
        front :=
          [("keyRec 1: the key's root in key.parsed.bin has 32 bytes", k.root.size == 32),
            ("keyRec 2: the key's table has 2^v * s answers", k.answers.length == 2 ^ v * s),
            ("keyRec 3: the seeds' file has s seeds of lg coordinates",
              sd.length == s && sd.all fun y => y.1.length == lg)] }

def keyRecS (kb sb : ByteArray) : Except String (KeyRec srS.P.v 19 1) := keyRecOf srS.P.v 19 1 kb sb
def keyRecD (kb sb : ByteArray) : Except String (KeyRec frS.P.v 29 1) := keyRecOf frS.P.v 29 1 kb sb

/-- The rows entryIn 5 and 6. -/
def tieRows {v lg s : ℕ} (n : Laid v lg s) (k : KeyRec v lg s) : List (String × Bool) :=
  [("entryIn 5: the key's root in key.parsed.bin has 32 bytes", k.root.size == 32),
    ("entryIn 6: the leaf file's copy of the first table is the parsed key file's: root and \
        answers",
      n.L.root0 == k.root && n.L.answers0 == k.answers)]

open VerifiableInference.OnPublicFiles in
/-- **All in one, the small size**: cm, rcd, e, and entryIn 1 to 6 in order, then keyRec 2 | 3. The
  rows are the caller's to judge. -/
def entryAllS (c kb sb leaf seeds : ByteArray) :
    Except String (Dig 256 × RecP NZ srS.P.v 19 1 × SlotsBehindCutDS.EntryIn × List (String × Bool))
        :=
  match keyRecS kb sb, laidOf srS.P.v 19 1 OnBytes.Flat.dsSmall.length c leaf seeds with
  | .error w, _ => .error w
  | _, .error w => .error w
  | .ok k, .ok n => .ok (k.cm, k.rcd, n.inDS, n.front ++ tieRows n k ++ k.front.drop 1)

open VerifiableInference.OnPublicFiles in
/-- **All in one, the full size.** -/
def entryAllD (c kb sb leaf seeds : ByteArray) :
    Except String (Dig 256 × RecP NZ frS.P.v 29 1 × SlotsBehindCutD.EntryIn × List (String × Bool))
        :=
  match keyRecD kb sb, laidOf frS.P.v 29 1 OnBytes.Flat.dsFull.length c leaf seeds with
  | .error w, _ => .error w
  | _, .error w => .error w
  | .ok k, .ok n => .ok (k.cm, k.rcd, n.inD, n.front ++ tieRows n k ++ k.front.drop 1)

/-! ## The controls, on the table alone -/

/-- A digest with the bit at place 0 flipped. -/
def flipD (d : Dig 256) : Dig 256 := fun i => if i.val = 0 then !d i else d i

/-- `f` at a list's first member; the empty list stays. -/
def headBy {α : Type} (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l

/-- `f` at the row of a table's first entry; the empty table stays. -/
def firstRow (f : TypedOracleCompiler.Slice.Row → TypedOracleCompiler.Slice.Row) : TabE → TabE
  | z :: l => (z.1, f z.2) :: l
  | [] => []

/-- Three changed tables: name · what is foretold · the turn. -/
def tabControls : List (String × String × (TabE → TabE)) :=
  [("unread row: one row more, at a leaf of the first tree at which nothing is read",
      "NO, at [strict 3]",
      oneMore (fun l t _ => freePlace l t)),
    ("read digest: one bit of the first digest of the first row's path is flipped",
        "NO, at [after 3]",
      firstRow (fun r => (r.1, r.2.1, headBy flipD r.2.2))),
    ("column: 1 is added to the first word of the first row's column", "NO, \"after 3\" among them",
      firstRow (fun r => (headBy (· + 1) r.1, r.2.1, r.2.2)))]

/-- Their condition: the first row's sibling leaf is not opened too. -/
def controlsFitT (tab : TabE) : Bool :=
  match tab with
  | z :: _ => !((tab.filter fun w => w.1.1 == z.1.1).any fun w => w.1.2 == (z.1.2 ^^^ 1))
  | [] => false

open VerifiableInference.OnPublicFiles in
def entryControlsS : List (String × String × (SlotsBehindCutDS.EntryIn → SlotsBehindCutDS.EntryIn))
    :=
  tabControls.map fun k => (k.1, k.2.1, fun e => { e with tab := k.2.2 e.tab })
open VerifiableInference.OnPublicFiles in
def entryControlsD : List (String × String × (SlotsBehindCutD.EntryIn → SlotsBehindCutD.EntryIn)) :=
  tabControls.map fun k => (k.1, k.2.1, fun e => { e with tab := k.2.2 e.tab })
open VerifiableInference.OnPublicFiles in
def controlsFitS (e : SlotsBehindCutDS.EntryIn) : Bool := controlsFitT e.tab
open VerifiableInference.OnPublicFiles in
def controlsFitD (e : SlotsBehindCutD.EntryIn) : Bool := controlsFitT e.tab

/-- A fourth control: in a
  record the first coordinate of the first seed's point is set to 7. FORETOLD: NO, at [after 5]
  alone. -/
def seedTurned {v lg s : ℕ} (r : RecP NZ v lg s) : RecP NZ v lg s :=
  ((fun i => if i.val = 0 then
      ((fun j => if j.val = 0 then toE (7, 0, 0) else (r.1 i).1 j), (r.1 i).2)
    else r.1 i), r.2)

end PV.EntryInOf
