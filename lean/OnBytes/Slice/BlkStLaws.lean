-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkStLaws.lean: what the changes of a statement leave of its groups and of its oracle
messages.

The laws on runs of a block give the statement after a call as a named function of the statement
before it: one more group (`withGroup`), oracle messages that are sent (`stSent`), an oracle message
that is admitted with its sample rows (`admitted`) or joins a group (`withMessageInGroup`), one more open row
(`withRow`), the beginning of a proximity test (`begun`). This file looks such statements up: which
group has a given number, which oracle message, which codes. It also carries what was tested of an
open row to a later statement, and turns it into the conditions of the laws on batching
(OnBytes/Iop/RowLaws.lean: `RowFits`).

Main definition: `withGroup`.
Main theorems.
 `newGroup_inv`                       a run of the call that makes a group.
 `withGroup_group`, `joined_group`, `withRow_group`   the group after a change.
 `stSent_new`, `admitted_same`, `admitted_other`, `joined_same`, `joined_other`
                                      an oracle message after a change.
 `tableBits_congr`, `RowChecked.congr`   what was tested of a row, in a later statement.
 `closeLedgers_shape`, `begun_rowBits`   the beginning of a test changes no shape.
 `rowFits_of_checked`, `rowFits_congr`   the conditions of the laws on batching.
Not claimed. Nothing on what a row's coefficients are. Nothing on soundness.
-/
import OnBytes.Iop.RowLaws
import OnBytes.Slice.BlkCalls
import OnBytes.Slice.BlkSendRun

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## One more group -/

/-- The statement with one more group, which has no member and no row. -/
def withGroup (S : Statement) (code maskCode : Nat) : Statement :=
  { S with groups := S.groups.push { code := code, maskCode := maskCode } }

/-- A new group gets the next number. -/
theorem newGroup_inv (code maskCode g : Nat) (c c' : Ctx)
    (h : (Blk.newGroup code maskCode).Yields c g c') :
    g = c.st.groups.size ∧ c' = { c with st := withGroup c.st code maskCode } := by
  unfold Blk.newGroup at h
  obtain ⟨S, c1, h1, a1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨eS, e1⟩ := (Blk.yields_statement _ _ _).1 h1
  obtain ⟨_, c2, h2, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 a1
  obtain ⟨_, e2⟩ := (Blk.yields_get _ _ _ _).1 h2
  obtain ⟨_, c3, h3, a3⟩ := (Blk.yields_bind _ _ _ _ _).1 a2
  obtain ⟨_, e3⟩ := (Blk.yields_get _ _ _ _).1 h3
  obtain ⟨_, c4, h4, a4⟩ := (Blk.yields_bind _ _ _ _ _).1 a3
  obtain ⟨_, e4⟩ := (Blk.yields_must _ _ _).1 h4
  obtain ⟨_, c5, h5, a5⟩ := (Blk.yields_bind _ _ _ _ _).1 a4
  have e5 := (yields_setStatement _ _ _).1 h5
  obtain ⟨e6, e7⟩ := (Blk.yields_pure _ _ _ _).1 a5
  refine ⟨by rw [e6, eS], ?_⟩
  rw [e7, e5, e4, e3, e2, e1, eS]
  rfl

/-- The new group has the next number. -/
theorem withGroup_group (S : Statement) (a b : Nat) :
    (withGroup S a b).groups[S.groups.size]? = some { code := a, maskCode := b } := by
  simp [withGroup]

/-- A new group changes no oracle message and no code. -/
theorem withGroup_oracles (S : Statement) (a b : Nat) :
    (withGroup S a b).oracles = S.oracles ∧ (withGroup S a b).codes = S.codes := ⟨rfl, rfl⟩

/-! ## Oracle messages that are sent -/

/-- Oracle messages that are sent change no group and no code. -/
theorem stSent_groups (S : Statement) (sent : Array OracleNotice) :
    (stSent S sent).groups = S.groups ∧ (stSent S sent).codes = S.codes := ⟨rfl, rfl⟩

/-- Oracle message number i of those that are sent, in the statement: its shape, and nothing else
yet. -/
theorem stSent_new (S : Statement) (sent : Array OracleNotice) (i : Nat) :
    (stSent S sent).oracles[S.oracles.size + i]? =
      (sent[i]?).map fun n => { shape := n.shape } := by
  simp [stSent, Array.getElem?_append_right]

/-- The earlier oracle messages are as they were. -/
theorem stSent_old (S : Statement) (sent : Array OracleNotice) (o : Nat)
    (h : o < S.oracles.size) : (stSent S sent).oracles[o]? = S.oracles[o]? := by
  simp [stSent, Array.getElem?_append_left h]

/-! ## An oracle message that is admitted -/

/-- Admitting an oracle message changes no group and no code. -/
theorem admitted_groups (S : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) :
    (admitted S o s p rows).groups = S.groups ∧ (admitted S o s p rows).codes = S.codes :=
  ⟨rfl, rfl⟩

/-- The oracle message that is admitted: sampled, with its sample rows, its pad and a new ledger. -/
theorem admitted_same (S : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) (x : Oracle) (h : S.oracles[o]? = some x) :
    (admitted S o s p rows).oracles[o]? = some { x with
      sampled := true, sampleRows := rows, pad := p.map fun q => (q.part, q.index),
      ledger := freshLedger S.codes s } := by
  simp [admitted, Array.getElem?_modify, h]

/-- The other oracle messages are as they were. -/
theorem admitted_other (S : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) (o' : Nat) (h : o ≠ o') :
    (admitted S o s p rows).oracles[o']? = S.oracles[o']? := by
  simp [admitted, Array.getElem?_modify, h]

/-! ## An oracle message that joins a group -/

/-- Joining a group changes no code. -/
theorem joined_codes (S : Statement) (g o : Nat) (k : Bool) (G : Group) :
    (withMessageInGroup S g o k G).codes = S.codes := rfl

/-- The group that an oracle message joins: the new member is entered at its place by number. -/
theorem joined_group (S : Statement) (g o : Nat) (k : Bool) (G : Group)
    (h : S.groups[g]? = some G) :
    (withMessageInGroup S g o k G).groups[g]? = some { G with
                  members := G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
                  kept := G.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k } := by
  simp [withMessageInGroup, Array.getElem?_modify, h]

/-- The oracle message that joins a group notes the group. -/
theorem joined_same (S : Statement) (g o : Nat) (k : Bool) (G : Group) (x : Oracle)
    (h : S.oracles[o]? = some x) :
    (withMessageInGroup S g o k G).oracles[o]? = some { x with groups := x.groups ++ [g] } := by
  simp [withMessageInGroup, Array.getElem?_modify, h]

/-- The other oracle messages are as they were. -/
theorem joined_other (S : Statement) (g o : Nat) (k : Bool) (G : Group) (o' : Nat) (h : o ≠ o') :
    (withMessageInGroup S g o k G).oracles[o']? = S.oracles[o']? := by
  simp [withMessageInGroup, Array.getElem?_modify, h]

/-! ## One more row -/

/-- The group that gets one more open row: the row is appended to its rows. -/
theorem withRow_group (S : Statement) (g : Nat) (r : Row) (G : Group)
    (h : S.groups[g]? = some G) :
    (withRow S g r).groups[g]? = some { G with rows := G.rows.push r } := by
  simp [withRow, Array.getElem?_modify, h]

/-- One more open row changes no oracle message and no code. -/
theorem withRow_oracles (S : Statement) (g : Nat) (r : Row) :
    (withRow S g r).oracles = S.oracles ∧ (withRow S g r).codes = S.codes := ⟨rfl, rfl⟩

/-! ## What was tested of a row, in a later statement -/

/-- The index bits of a table depend on the oracle messages and the codes alone. -/
theorem tableBits_congr {S S' : Statement} (h1 : S'.oracles = S.oracles) (h2 : S'.codes = S.codes)
    (o : Nat) (part : Part) : S'.tableBits o part = S.tableBits o part := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [h1, h2]

/-- What was tested of a row holds in every statement with the same oracle messages and codes. -/
theorem RowChecked.congr {S S' : Statement} {row : Row} (h1 : S'.oracles = S.oracles)
    (h2 : S'.codes = S.codes) (h : RowChecked S row) : RowChecked S' row :=
  ⟨fun t ht => (h.terms t ht).trans (tableBits_congr h1 h2 _ _).symm, h.runs,
    fun f hf => by rw [tableBits_congr h1 h2]; exact h.forms f hf⟩

/-! ## The statement after the beginning of the test -/

/-- Closing ledgers changes no shape. -/
theorem closeLedgers_shape : ∀ (l : List Nat) (S : Statement) (o : Nat),
    ((closeLedgers S l).oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape)
  | [], _, _ => rfl
  | a :: l, S, o => by
    show ((closeLedgers _ l).oracles[o]?).map (·.shape) = _
    rw [closeLedgers_shape l]
    simp only [Array.getElem?_modify]
    split
    · cases S.oracles[o]? <;> rfl
    · rfl

/-- Closing ledgers changes no code. -/
theorem closeLedgers_codes : ∀ (l : List Nat) (S : Statement), (closeLedgers S l).codes = S.codes
  | [], _ => rfl
  | _ :: l, _ => closeLedgers_codes l _

/-- The beginning of a test changes no number of row bits. -/
theorem begun_rowBits (S : Statement) (g : Nat) (G : Group) (o : Nat) (part : Part) :
    (begun S g G).rowBits o part = S.rowBits o part := by
  have h := closeLedgers_shape G.members.toList S o
  unfold Statement.rowBits
  show (match (closeLedgers S G.members.toList).oracles[o]? with
    | some x => ceilLog2 (x.shape.rows part)
    | none => 0) = _
  cases h1 : (closeLedgers S G.members.toList).oracles[o]? with
  | none =>
    cases h2 : S.oracles[o]? with
    | none => rfl
    | some y =>
      rw [h1, h2] at h
      cases h
  | some x =>
    cases h2 : S.oracles[o]? with
    | none =>
      rw [h1, h2] at h
      cases h
    | some y =>
      rw [h1, h2] at h
      have e : x.shape = y.shape := Option.some.inj h
      show ceilLog2 (x.shape.rows part) = ceilLog2 (y.shape.rows part)
      rw [e]

/-! ## The conditions on rows -/

/-- What the adding of an open row has tested of it gives the conditions of the laws on batching. -/
theorem rowFits_of_checked {S : Statement} {row : Row} (h : RowChecked S row) : RowFits S row := by
  refine ⟨fun t ht => ?_, fun w hw => h.runs w hw, fun f hf v hv => ?_⟩
  · rw [h.terms t ht]
    exact Nat.le_add_right _ _
  · have h1 := h.forms f hf
    unfold Form.fits at h1
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h1
    rw [(h1.1 v hv).1]
    exact Nat.le_add_right _ _

/-- The conditions look at the statement's numbers of row bits alone. -/
theorem rowFits_congr {S S' : Statement} {row : Row}
    (hb : ∀ o part, S'.rowBits o part = S.rowBits o part) (h : RowFits S row) : RowFits S' row :=
  ⟨fun t ht => by rw [hb]; exact h.terms t ht, h.runs,
    fun f hf v hv => by rw [hb]; exact h.forms f hf v hv⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.newGroup_inv
#print axioms OnBytes.Slice.withGroup_group
#print axioms OnBytes.Slice.withGroup_oracles
#print axioms OnBytes.Slice.stSent_groups
#print axioms OnBytes.Slice.stSent_new
#print axioms OnBytes.Slice.stSent_old
#print axioms OnBytes.Slice.admitted_groups
#print axioms OnBytes.Slice.admitted_same
#print axioms OnBytes.Slice.admitted_other
#print axioms OnBytes.Slice.joined_codes
#print axioms OnBytes.Slice.joined_group
#print axioms OnBytes.Slice.joined_same
#print axioms OnBytes.Slice.joined_other
#print axioms OnBytes.Slice.withRow_group
#print axioms OnBytes.Slice.withRow_oracles
#print axioms OnBytes.Slice.tableBits_congr
#print axioms OnBytes.Slice.RowChecked.congr
#print axioms OnBytes.Slice.closeLedgers_shape
#print axioms OnBytes.Slice.closeLedgers_codes
#print axioms OnBytes.Slice.begun_rowBits
#print axioms OnBytes.Slice.rowFits_of_checked
#print axioms OnBytes.Slice.rowFits_congr
