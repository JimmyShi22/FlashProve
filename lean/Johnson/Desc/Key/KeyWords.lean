-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyWords.lean: the table of joints of the key file: the words in which its items are said: what it is for the committed matrix's entries to lie in their ranges, for a row on the matrix to hold, and
for an open row of a group to hold, at a witness. Definitions alone, free of any state: each takes public values (the plan's) and plain functions that read the witness. No Mathlib.
  KRead            how a witness is read: two base letters: tab (the stored table's message: row r, place i) · val (entry number i of a message's main | mask table). They read the witness and nothing that was heard.
  sumE             a sum over 0 .. n - 1
  matAt S tab      the matrix in the table [OnBytes/Iop/Lin.lean:41-44: «the entry (y, j + 2^kLo r) of M is at place j + 2^kLo y of row r of the table»; held against the code, by reading: linFoldRow (Lin.lean:151-158) reads the folded row at eq(psi.take kLo ++ zeta): the low kLo bits of a place are the column's, the next kRow the matrix's row's; gamma := psi.drop kLo folds the table's rows]
  keyAt l mat r t c  a key [OnBytes/Key/Ranges.lean:9-19: key(place, column) = offset + Σ_q digitWeight[q] · M[row of (place, q)][column]; for digit q the place firstPlace + t of a run reads the row firstRow + t + q · stride; held against the program's own code, by reading: Wf.pendingRow (OnBytes/Iop/Wf.lean:246-262) lays the weight e[firstPlace + i] · digitWeight[q] on the row firstRow + q · stride + i]
  InRange m l mat  **every key of every place that a run covers is one of 0 .. 2^d - 1** (a place that no run covers is padding: a public key: it reads nothing of the matrix)
  weightAt · TensorRowHolds m mat mk x   a row on the matrix holds [OnBytes/Iop/Batt.lean:6-8: ⟨g ⊗ eq(psi, ·), M⟩ + (a linear form in mask entries) = target], the sum over the real rows alone [Lin.lean:139-141]
  RowHolds St val r   an open row of a group holds: the sum over all entries of all oracle messages of the statement of (the row's own coefficient there: Row.coefficient) · (the entry) is the row's target
  VIs m g mat v    V = gᵀM at every column
Limits. The field's elements are the program's machine elements (E: three words; F: one). «Is» between two elements is the letter same (KRead.same: «they read as one element of the field»), not equality of words. The sums and
products are still the program's machine operations: that these read as the field's at words that are not below the prime is owed by whoever fills same: every law over these sentences still carries the words' test. A key is an element of the field: that it is the integer that it looks like is the reader's conclusion from the ranges
(Ranges.lean:12-14): not said here. No law is stated. Nothing on soundness.
-/
import OnBytes.Iop.Wf
import OnBytes.Iop.Lin
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Params (WfRun WfPart WfLookup LinShape)

/-- **How a witness is read.** -/
structure KRead (Cells M : Type) where
  /-- the stored table's message: row r, place i -/
  tab : Cells → Nat → Nat → F
  /-- entry number i of a message's main | mask table, in the numbering of Statement.tableBits -/
  val : M → Part → Nat → E
  /-- WHICH TABLE OF THE WITNESS's MESSAGE k THE ROWS AND THE NAMED CLAIMS READ. Johnson/Desc/Msg.lean (Wit.pad · Reading.lay): «THROUGH THE TABLE, ALWAYS: NOBODY READS w.msg k OR w.pad j t BARE»: PIN pins lay j t (w.msg k) (w.pad j t): at a pad's
  places w.msg k is pinned by nothing, and a sample row reads just these. It stands for the table that PIN pins: msgOf G w at message k's one seat (KeyTies.ReadsPinned says so, in the promise). -/
  of : VerifiableInference.Desc.Wit Cells Unit M → Nat → M
  /-- TWO MACHINE ELEMENTS READ AS ONE ELEMENT OF THE FIELD. Every «is» between elements in the table's sentences is THIS, not equality of words: words equal ⟹ readings equal, NOT the converse ((p, 0, 0) reads as 0): a count in the field gives «reads as»,
  never «the words are equal». It is meant as the library's reading of a word: ρ a = ρ b. AT same := Eq the sentences speak of equality of words. -/
  same : E → E → Prop

/-- A sum over 0 .. n - 1. -/
def sumE (n : Nat) (f : Nat → E) : E := (List.range n).foldl (fun s i => addE s (f i)) zeroE

/-- **The matrix in the table.** -/
def matAt (S : LinShape) (tab : Nat → Nat → F) (y c : Nat) : F := tab (c / 2 ^ S.kLo) (c % 2 ^ S.kLo + 2 ^ S.kLo * y)

/-- **A key**: of the place firstPlace + t of the run r, at the column c. -/
def keyAt (l : WfLookup) (mat : Nat → Nat → F) (r : WfRun) (t c : Nat) : E :=
  l.digitWeight.zipIdx.foldl (fun s q => addE s (mulE (ofF q.1) (ofF (mat (r.firstRow + t + q.2 * r.stride) c)))) (ofF l.offset)

/-- **The lookup's relation.** -/
def InRange (same : E → E → Prop) (m : Wf.Matrix) (l : WfLookup) (mat : Nat → Nat → F) : Prop :=
  ∀ p ∈ l.parts, ∀ r ∈ p.runs, ∀ t, t < r.places → ∀ c, c < 2 ^ m.kCol → ∃ v, v < 2 ^ l.d ∧ same (keyAt l mat r t c) (ofF v.toUInt64)

/-- The weight of the matrix's row y: the sum of the vectors' entries there. -/
def weightAt (g : List Tensor) (y : Nat) : E := g.foldl (fun s t => addE s (t.entry y)) zeroE

/-- A linear form in mask entries, at the entries' values. -/
def formAt (mk : Slot → E) (f : MaskForm) : E := f.foldl (fun s x => addE s (mulE x.2 (mk x.1))) zeroE

/-- **A row on the matrix holds.** -/
def TensorRowHolds (same : E → E → Prop) (m : Wf.Matrix) (mat : Nat → Nat → F) (mk : Slot → E) (x : TensorRow) : Prop :=
  same (addE (sumE m.rows fun y => sumE (2 ^ m.kCol) fun c => mulE (mulE (weightAt x.g y) ((Tensor.eq x.psi).entry c)) (ofF (mat y c))) (formAt mk x.masks)) x.target

/-- **An open row of a group holds.** val o: the entries of the statement's oracle message number o. -/
def RowHolds (same : E → E → Prop) (St : Statement) (val : Nat → Part → Nat → E) (r : OnBytes.Row) : Prop :=
  same (sumE St.oracles.size (fun o =>
    addE (sumE (2 ^ St.tableBits o .main) fun i => mulE (r.coefficient o .main i) (val o .main i))
      (sumE (2 ^ St.tableBits o .mask) fun i => mulE (r.coefficient o .mask i) (val o .mask i)))) r.target

/-- **V = gᵀM.** v c: the entry of V for the column c. -/
def VIs (same : E → E → Prop) (m : Wf.Matrix) (g : List Tensor) (mat : Nat → Nat → F) (v : Nat → E) : Prop :=
  ∀ c, c < 2 ^ m.kCol → same (v c) (sumE m.rows fun y => mulE (weightAt g y) (ofF (mat y c)))

/-! ## Silly members: each sentence is tried before it is leaned on (by evaluation at a toy) -/

/-- A toy lookup: one digit of weight 1, offset 0, d = 1 (the range 0 | 1), one part, one run of two places from row 0. -/
def toyL : WfLookup := { d := 1, mu := 1, live := 0, digitWeight := [1], offset := 0, paddingKey := 0, parts := [{ logPlaces := 1, runs := [{ firstPlace := 0, firstRow := 0, places := 2, stride := 0 }] }], firstBound := [] }

/-- InRange with code, at a toy: for the trials alone. -/
def inRangeB (m : Wf.Matrix) (l : WfLookup) (mat : Nat → Nat → F) : Bool :=
  l.parts.all fun p => p.runs.all fun r => (List.range r.places).all fun t => (List.range (2 ^ m.kCol)).all fun c =>
    (List.range (2 ^ l.d)).any fun v => keyAt l mat r t c == ofF v.toUInt64

#eval inRangeB ⟨1, 2⟩ toyL (fun _ _ => 0)                                  -- all entries 0: due true
#eval inRangeB ⟨1, 2⟩ toyL (fun y c => if y == 1 && c == 1 then 1 else 0)  -- entries 0 | 1: due true
#eval inRangeB ⟨1, 2⟩ toyL (fun y c => if y == 1 && c == 1 then 2 else 0)  -- one entry 2: due false: THE SENTENCE IS NOT «true everywhere»
#eval inRangeB ⟨1, 2⟩ toyL (fun y _ => if y == 2 then 7 else 0)            -- an entry out of range IN A ROW THAT NO RUN READS: due true: what «some lookup reaches every row» (fileOk) is there for

end VerifiableInference.Desc.Key
