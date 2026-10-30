-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/RowCode.lean: under which codes the rows of an oracle message stand. Definitions, and three
small facts. It imports OnBytes/Iop/Ground.lean and nothing else, so that whoever counts a
verifier's reads of a row and whoever counts the encoding randomness that a prover lays under it can
call one and the same function.

A code (`OnBytes.Code`) is three numbers: the logarithm of its length, the entries of a message, and
r, the elements of encoding randomness OF ONE ROW.

FOR WHOEVER COUNTS WHAT A SENDER LAYS: `dueOf`.
  `RowsDue`: rows of one sort of one oracle message: how many rows; the words of a symbol (1: rows
    over the base field; 3: over the extension field); their code.
  **`dueOf codes n`**: the rows of the oracle message that the notice n announces: its main rows, if
    it has any, then its mask rows, if it has any, which are over the extension field. NOTHING if a
    sort of rows that it has names a code that the list lacks: the library's verifier rejects such a
    shape (`shapeOk`, OnBytes/Iop/Ground.lean).
  `mainDue`, `maskDue`: the two sorts one by one: nothing due, rows due, or a code that is not
    there.
  `RowsDue.tails`: rows times r: the elements of encoding randomness of these rows together, each an
    element of the rows' own field.
FOR WHOEVER HOLDS A COUNT OF READS AGAINST r: `rowsOf`.
  `rowsOf codes n`: the codes alone: ONE ENTRY FOR EACH SORT OF ROWS, NOT FOR EACH ROW. A code that
    the list lacks counts as the code with all three numbers 0 (`default_code`): a reader's count
    then fails.
THE TWO BARE LOOK-UPS: `mainOf`, `maskOf`: the member of the list of main (mask) codes whose number
  the notice's shape names.

TRAPS.
- THE SUM OF r OVER `rowsOf` IS NOT WHAT A SENDER OWES: that is the sum of `RowsDue.tails` over
  `dueOf` (the library's count: `port_Q`, Johnson/Pack/Port.lean), and its summands are elements of
  unlike fields.
- `mainOf` AND `maskOf` DO NOT LOOK AT THE NUMBERS OF ROWS. A shape without mask rows may name the
  mask code 0, which is what the record lays there if nothing is said: `maskOf` then returns the
  list's first mask code, though the message has no such row.
- `rowsOf` puts ⟨0, 0, 0⟩ for a missing code. Read as «0 elements due» that would be wrong for a
  sender.
- THAT `dueOf` RETURNS A LIST DOES NOT SAY THAT THE VERIFIER TAKES THE SHAPE: `shapeOk` has two
  clauses more. A message without any row gets the empty list here and is rejected there; a number
  of words of a main row's symbol other than 1 or 3 is handed on here as it stands and is rejected
  there.
- IN WHICH FIELD THE ENCODING RANDOMNESS LIES: in the rows' own. The library's code of a shape
  (`portCode`, Johnson/Pack/Port.lean) has it over the extension field BY TYPE, whatever the rows'
  field; but a word whose main rows are sent over the base field can be sent only if their encoding
  randomness lies in the base field too: the library's `Sendable` asks it
  (Johnson/RunOne/KeyMember.lean; Johnson/Pack/TwoPads.lean). So whoever types a sender at that code
  samples it in the base field there, as `RowsDue` counts it.

What is shown. `default_code`. `rowsOf_of_due`: where `dueOf` returns a list, `rowsOf` is the list
of its codes. `due_isSome`: `dueOf` returns a list just if each sort of rows that the message has
names a code that is there.

Limits. That a verifier or a prover treats the rows so is said by nothing here. Encoding randomness
alone is counted: pads, mask rows' messages and what else a sender samples are not.


-/
import OnBytes.Iop.Ground

set_option autoImplicit false

namespace AtPublicFiles.RowCode
open OnBytes

/-- The member of the list of main codes whose number the shape names. It does not ask whether the
message has main rows. -/
def mainOf (codes : Codes) (n : OracleNotice) : Option Code := codes.base[n.shape.code]?

/-- The member of the list of mask codes whose number the shape names. It does not ask whether the
message has mask rows. -/
def maskOf (codes : Codes) (n : OracleNotice) : Option Code := codes.mask[n.shape.maskCode]?

/-- The codes of the message's rows: one entry for each sort of rows that it has. -/
def rowsOf (codes : Codes) (n : OracleNotice) : List Code :=
  (if n.shape.mainRows = 0 then [] else [(mainOf codes n).getD default]) ++
    (if n.shape.maskRows = 0 then [] else [(maskOf codes n).getD default])

/-- The code that stands in for a missing one has all three numbers 0. -/
theorem default_code : (default : Code) = ⟨0, 0, 0⟩ := rfl

/-- Rows of one sort of one oracle message. -/
structure RowsDue where
  /-- how many rows -/
  rows : Nat
  /-- the words of a symbol: 1: over the base field; 3: over the extension field -/
  deg : Nat
  code : Code
  deriving DecidableEq, Repr

/-- The elements of encoding randomness of these rows together, in the rows' own field. -/
def RowsDue.tails (d : RowsDue) : Nat := d.rows * d.code.r

/-- The main rows: no entry if there are none; nothing if their code is missing. -/
def mainDue (codes : Codes) (n : OracleNotice) : Option (List RowsDue) :=
  if n.shape.mainRows = 0 then some []
  else (mainOf codes n).map fun c => [⟨n.shape.mainRows, n.shape.mainDeg, c⟩]

/-- The mask rows, which are over the extension field: the like. -/
def maskDue (codes : Codes) (n : OracleNotice) : Option (List RowsDue) :=
  if n.shape.maskRows = 0 then some []
  else (maskOf codes n).map fun c => [⟨n.shape.maskRows, 3, c⟩]

/-- **The rows of an oracle message, sort by sort, each with its number, its field and its code.**
-/
def dueOf (codes : Codes) (n : OracleNotice) : Option (List RowsDue) :=
  match mainDue codes n, maskDue codes n with
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- Where `dueOf` returns a list, `rowsOf` is the list of its codes. -/
theorem rowsOf_of_due {codes : Codes} {n : OracleNotice} {l : List RowsDue}
    (h : dueOf codes n = some l) : rowsOf codes n = l.map (·.code) := by
  unfold dueOf at h
  split at h
  · rename_i a b ha hb
    obtain rfl : a ++ b = l := Option.some.inj h
    rw [List.map_append]
    unfold rowsOf
    congr 1
    · unfold mainDue at ha
      split at ha
      · rename_i h0
        obtain rfl : [] = a := Option.some.inj ha
        rw [if_pos h0]
        rfl
      · rename_i h0
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 ha
        rw [hc, if_neg h0]
        rfl
    · unfold maskDue at hb
      split at hb
      · rename_i h0
        obtain rfl : [] = b := Option.some.inj hb
        rw [if_pos h0]
        rfl
      · rename_i h0
        obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hb
        rw [hc, if_neg h0]
        rfl
  · cases h

/-- `dueOf` returns a list just if each sort of rows that the message has names a code that is
there. -/
theorem due_isSome (codes : Codes) (n : OracleNotice) :
    (dueOf codes n).isSome = true ↔
      (n.shape.mainRows = 0 ∨ n.shape.code < codes.base.size) ∧
        (n.shape.maskRows = 0 ∨ n.shape.maskCode < codes.mask.size) := by
  have e1 : (mainDue codes n).isSome = true ↔
      (n.shape.mainRows = 0 ∨ n.shape.code < codes.base.size) := by
    unfold mainDue mainOf
    by_cases h : n.shape.mainRows = 0
    · simp [h]
    · simp [h]
  have e2 : (maskDue codes n).isSome = true ↔
      (n.shape.maskRows = 0 ∨ n.shape.maskCode < codes.mask.size) := by
    unfold maskDue maskOf
    by_cases h : n.shape.maskRows = 0
    · simp [h]
    · simp [h]
  rw [← e1, ← e2]
  unfold dueOf
  cases mainDue codes n <;> cases maskDue codes n <;> simp

end AtPublicFiles.RowCode

#print axioms AtPublicFiles.RowCode.default_code
#print axioms AtPublicFiles.RowCode.rowsOf_of_due
#print axioms AtPublicFiles.RowCode.due_isSome
