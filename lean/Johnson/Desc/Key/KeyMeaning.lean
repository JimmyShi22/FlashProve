-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyMeaning.lean: the table of joints of the key file: the first chain's items filled: what each item of Johnson/Desc/Key/KeyBorders.lean says, as a definition, in the words of
Johnson/Desc/Key/KeyWords.lean, of a chain's state read through named readers alone. Definitions alone. No Mathlib.
Why readers. The state of the first chain lies in other files, so no field of a state is named here: `KReaders S` says what must be readable at a border; whoever owns the state fills it.

  KPlan        the plan's public values that the items read: the matrix's size · the shape of the test on the table · the lookups · which oracle message of the chain's statement is the witness's message k
  KReaders S   marked · st (the chain's statement: oracle messages with their sample rows; groups with their open rows) · grpB · rowsAt l (lookup l's rows as they lie behind its layer) · keysAt l (its pending rows on the
               matrix) · pile (the one row that the batching hands on) · eval (the row (Eval) as it lies) · g (the claim's row weights)
  valOf        the statement's oracle message number o, read off the witness
  meaning₁     **the filling**: unmarked · inRange · srow · rows · kclaims · grows · pile · claim 1 "Eval" · claim 1 "VIs" are definitions; letters, handed in: near (K12's files') · forms | worth (K3's files', at K3's general
               face) · every other claim (Johnson/Desc/Key/KeyMeaning23.lean's)
Every item that reads the state says «it is there, and …»: where a reader gives nothing the item is false, not free: so a border at which the state has lost what the item speaks of cannot be passed by silence.
Limits: KeyWords.lean's: machine elements; the words' test rides with every law. No law is stated. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyBorders
import Johnson.Desc.Key.KeyWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Params (WfLookup LinShape)

/-- **The plan's public values.** -/
structure KPlan where
  lin : LinShape
  lookups : List WfLookup
  /-- the number, in the chain's statement, of the witness's message k; nothing where the chain has none -/
  orc : Nat → Option Nat
  /-- the witness's message that the statement's oracle message number o is; nothing for a message that is no component (a fresh mask) -/
  num : Nat → Option Nat

def KPlan.m (K : KPlan) : Wf.Matrix := Wf.matrixOf K.lin

/-- **What must be readable of a state.** -/
structure KReaders (S : Type) where
  marked : S → Bool
  st : S → Statement
  grpB : S → Option Nat
  rowsAt : S → Nat → Option (List OnBytes.Row)
  keysAt : S → Nat → Option (List TensorRow)
  pile : S → Option TensorRow
  eval : S → Option OnBytes.Row
  g : S → Option (List Tensor)

section
variable {P S Cells M : Type} (K : KPlan) (R : KRead Cells M) (X : KReaders S)

/-- The statement's oracle message number o, read off the witness: 0 everywhere where it is no component. A ROW THAT NAMES SUCH A MESSAGE IS THEN READ AT 0 THERE: the rows of this chain's items name I, B and V alone: a
test on the plan is owed. -/
def valOf (w : Wit Cells Unit M) (o : Nat) (part : Part) (i : Nat) : E :=
  match K.num o with
  | some k => R.val (R.of w k) part i
  | none => zeroE

/-- A mask entry, read off the witness. -/
def mkOf (w : Wit Cells Unit M) (s : Slot) : E := valOf K R w s.oracle .mask s.index

/-- The matrix, read off the witness. -/
def matOf (w : Wit Cells Unit M) : Nat → Nat → F := matAt K.lin (R.tab w.cells)

/-- V's entry for the column c, read off the witness: at the place where the program's layout puts it. -/
def vOf (St : Statement) (w : Wit Cells Unit M) (c : Nat) : E := R.val (R.of w 2) .main ((linLayW St.codes K.lin).index c)

/-- **The first chain's items, filled.** -/
def meaning₁ (near : Nat → P × S → Strs → Prop) (forms worth : Nat → String → P × S → Strs → Wit Cells Unit M → Prop)
    (other : Nat → String → P × S → Strs → Wit Cells Unit M → Prop) : KMeaning P S (Wit Cells Unit M) where
  unmarked := fun a => X.marked a.2 = false
  inRange := fun l w => ∃ L, K.lookups[l]? = some L ∧ InRange R.same K.m L (matOf K R w)
  near := near
  srow := fun k a _ w => ∃ o x, K.orc k = some o ∧ (X.st a.2).oracles[o]? = some x ∧ x.sampled = true ∧ x.sampleRows.size ≠ 0 ∧
    ∀ r ∈ x.sampleRows.toList, RowHolds R.same (X.st a.2) (valOf K R w) r
  forms := forms
  worth := worth
  rows := fun l a _ w => ∃ rs, X.rowsAt a.2 l = some rs ∧ rs ≠ [] ∧ ∀ r ∈ rs, RowHolds R.same (X.st a.2) (valOf K R w) r
  kclaims := fun l a _ w => ∃ L ks, K.lookups[l]? = some L ∧ X.keysAt a.2 l = some ks ∧ ks.length = L.parts.length ∧ ∀ x ∈ ks, TensorRowHolds R.same K.m (matOf K R w) (mkOf K R w) x
  grows := fun a _ w => ∃ g G o x, X.grpB a.2 = some g ∧ (X.st a.2).groups[g]? = some G ∧ K.orc 1 = some o ∧ (X.st a.2).oracles[o]? = some x ∧ G.rows.size ≠ 0 ∧
    (∀ r ∈ G.rows.toList, RowHolds R.same (X.st a.2) (valOf K R w) r) ∧ ∀ r ∈ x.sampleRows.toList, RowHolds R.same (X.st a.2) (valOf K R w) r
  pile := fun a _ w => ∃ x, X.pile a.2 = some x ∧ TensorRowHolds R.same K.m (matOf K R w) (mkOf K R w) x
  claim := fun c n a y w =>
    if c = 1 ∧ n = "Eval" then ∃ r, X.eval a.2 = some r ∧ RowHolds R.same (X.st a.2) (valOf K R w) r
    else if c = 1 ∧ n = "VIs" then ∃ g, X.g a.2 = some g ∧ VIs R.same K.m g (matOf K R w) (vOf K R (X.st a.2) w)
    else other c n a y w

end

end VerifiableInference.Desc.Key
