-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/ShapeDefs.lean: kind K13: the types of the shapes of the first chain's state
that the kind's sub-protocols read, and the projections onto them. Definitions alone; no theorem. It
imports the library alone, so that a file that wants these types need not import the laws on them.

What lies where. Here: of the members' batching: `varsMark`, `RowSh`, `rowSh`, `MsgSh`, `Sh`; of the
sub-protocol behind W's commitment and of the first chain's last sub-protocol: `GrpSh`, `Msg4`,
`StSh`, `grpSh`, `msg4`, `stSh`, `ClaimSh`, `claimSh4`, `LaidSh`, `laidSh`, `Sh4`, `sh4`. In
Johnson/Desc/K13/Honest/Shape.lean: the projection `shOf` onto `Sh`, which calls a test of
Johnson/Desc/K13/Honest/Ready.lean (`atFinC`), the tests on `Sh` and their laws. In
Johnson/Desc/K13/Honest/ShapeM4.lean: the update on `Sh4` and its laws.
THE FIELDS' TYPES: numbers, Bools, lists, arrays, options and pairs of these; `Slot` (two numbers);
`OnBytes.Part` (one of two names); `OracleShape` (six numbers); `Ledger` (four numbers and a Bool);
`Codes` (arrays of codes, each of three numbers). NO ELEMENT OF A FIELD.

What is not claimed. That a number in a shape at a state of a run is made of no sent value and of no
coin: the types shut out field elements and nothing more. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.First (S)

/-! ## Of the members' batching -/

/-- **One mark for a list of numbers**: some v: the list is not empty and each of its members is v;
none: it is empty, or two of its members differ. -/
def varsMark : List Nat → Option Nat
  | [] => none
  | v :: t => if t.all (· == v) then some v else none

/-- **A row's shape.** OF THE ROW's WEIGHT VECTORS IT HOLDS TWO MARKS, AND NOT HOW MANY THERE ARE.
Why: the tests that later sub-protocols make on a row (`Batt.fits`, OnBytes/Iop/Batt.lean;
`memberRowsFit`, OnBytes/Iop/Lin.lean) read of them just this: there is one; each has so many
variables. Two rows that these tests cannot tell apart can have different numbers of weight vectors:
the library's `dryRow` (OnBytes/Iop/Wf.lean) has one where its `pendingRow` has one for each aligned
block of rows. The three cases: no weight vector (bare, none) · each has v variables (not bare, some
v) · two differ (not bare, none): there the marks also leave out which numbers they have, and in
which order. The fourth pair (bare, some v) can be written; `rowSh` never makes it. `bare` is NEEDED
for one test alone (`fitSh`, Shape.lean of this folder): `memberRowsFit` accepts a row without a
weight vector and rejects one whose weight vectors differ, so one mark could not say what that test
says. (`formSh`, and `claimSh` of ClaimShape.lean, read it too; at what `rowSh` makes of a pile that
the batching allows, `vars` alone would do there.) -/
structure RowSh where
  /-- the row has no weight vector -/
  bare : Bool
  /-- some v: the row has a weight vector, and each has v variables; none: it has none, or two
  differ -/
  vars : Option Nat
  /-- how many coordinates the column point has -/
  point : Nat
  /-- the slots that the mask form names -/
  slots : List Slot
  deriving DecidableEq, Repr

/-- Of a row. -/
def rowSh (r : TensorRow) : RowSh :=
  ⟨r.g.isEmpty, varsMark (r.g.map Tensor.vars), r.psi.length, r.masks.map (·.1)⟩

/-- An oracle message's shape and ledger. -/
structure MsgSh where
  shape : OracleShape
  ledger : Option Ledger
  deriving DecidableEq, Repr

/-- **The shape.** -/
structure Sh where
  /-- the chain is out of the finish and not yet at its end -/
  atFin : Bool
  /-- a reply was heard -/
  reply : Bool
  /-- no count of rows waits -/
  quiet : Bool
  /-- the number of the index masks' message -/
  index : Nat
  /-- the shapes of the rows on the pile, in their order -/
  pile : List RowSh
  /-- the statement's codes -/
  codes : Codes
  /-- the shape and the ledger of each oracle message of the statement, by its number -/
  msgs : Array MsgSh

/-! ## Of the sub-protocol behind W's commitment, and of the chain's last -/

/-- A group's shape: all but its rows, of which the number stays. -/
structure GrpSh where
  code : Nat
  maskCode : Nat
  members : Array Nat
  kept : Array Bool
  rows : Nat
  inRun : Bool

/-- A message's shape: its `OracleShape`, its mark, its list of groups, its pad's places. -/
structure Msg4 where
  shape : OracleShape
  sampled : Bool
  groups : List Nat
  pad : List (OnBytes.Part × Nat)

/-- The statement's shape. -/
structure StSh where
  codes : Codes
  msgs : Array Msg4
  groups : Array GrpSh

def grpSh (G : Group) : GrpSh := ⟨G.code, G.maskCode, G.members, G.kept, G.rows.size, G.inRun⟩

def msg4 (x : OnBytes.Oracle) : Msg4 := ⟨x.shape, x.sampled, x.groups, x.pad⟩

def stSh (St : Statement) : StSh := ⟨St.codes, St.oracles.map msg4, St.groups.map grpSh⟩

/-- The claim's shape: how many coordinates its point has; the places of its masks. -/
structure ClaimSh where
  point : Nat
  slots : List (Nat × OnBytes.Part × Nat)

def claimSh4 (c : LinClaim) : ClaimSh :=
  ⟨c.psi.length, c.masks.toList.map fun u => (u.oracle, u.part, u.index)⟩

/-- What is laid for the last chain, with the claim's shape. -/
structure LaidSh where
  w : Nat
  split : Nat
  own : Nat
  mask : Option Nat
  claim : ClaimSh

def laidSh (l : LinFirst) : LaidSh := ⟨l.w, l.split, l.own, l.mask, claimSh4 l.claim⟩

/-- **The state's shape**, as far as `rowsB` reads and writes it. -/
structure Sh4 where
  /-- the chain stands at its end -/
  atEnd : Bool
  /-- the numbers handed on -/
  ids : Array Nat
  laid : Option LaidSh
  /-- the count of rows that is owed -/
  owed : Option Nat
  st : StSh

def sh4 (s : S) : Sh4 :=
  match s.here with
  | .mem o => ⟨true, o.ids, o.lin.map laidSh, s.rowsOwed, stSh s.st⟩
  | _ => ⟨false, #[], none, s.rowsOwed, stSh s.st⟩

end VerifiableInference.Desc.K13.Honest
