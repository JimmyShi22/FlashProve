-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LooksAtPlan.lean: the public records of the two lookups of a key file of full size, as
they are written out in Cb/Pv/KeyLookup/FullPub.lean, are the records of the lookups that the
planner computes from the full size's 32 lines and ten sizes of the model.

Cb/Pv/KeyLookup/FullPub.lean writes two records, pubFull₁ and pubFull₂, and
Johnson/Top/H/KeyRangesFull.lean two lookups of the item "ranges", lk0Full and lk1Full. Both were
typed after a print of the planner. Here the planner's own functions are evaluated by Lean's kernel.

The planner's way to a key's lookups has three steps that compute and many tests that only refuse:
the layout of the committed matrix (Model.wsLayOf), what the proof of the ranges looks up
(Plan.shapeOfLayout), and the parts and planes (Plan.rangesLines). looksOf is these three steps in a
row. What Plan.keySized returns holds looksOf's lookups (looks_of_keySized: at all lines and sizes).

Main names.
  rangesSized_lookups, keySized_lookups   the sizing hands the lines' lookups, the message's number
                    and the matrix's size on as they are.
  keySized_onceKCol the matrix that the blocks of a chain take (Wf.matrixOf of the shape of the test
                    on the table) has the lines' number of column variables.
  looksOf l w p3    the number of column variables, the lookups and the message's number, from the
                    lines l, the sizes w and "the model has layers with experts".
  looks_of_keySized what Plan.keySized returns holds these.
  wsFull            the ten sizes of the full size.
  looksOf_full      looksOf Params.recordLines wsFull true = some (18, [lk0Full, lk1Full], 1): by
                    the kernel's evaluation.
  pub_lk0, pub_lk1  the record made of lk0Full (lk1Full) at 18 column variables is pubFull₁
                    (pubFull₂): by the kernel's evaluation.
  pubs_full         so: at every key's sizes that Plan.keySized returns from these lines and the
                    layout of these sizes, the lookups' records are [pubFull₁, pubFull₂].
  looksOf_control_order, looksOf_control_dial, looksOf_control_layers   three controls: the written
                    lookups in the other order, another value of the line ranges-part, a model of
                    two layers: the equation fails.

Limits. One direction: from a planner that returns; that it returns at these numbers is not shown
here: a trial to have the kernel evaluate "Plan.keySized returns" at them did not go through, and
why was not found out (Johnson/Top/H/KeyRangesThm.lean says that the kernel does not reduce
List.mergeSort, by which the sizing's tests sort; that this is the cause here was not shown). A
control at 46 layers in the place of 48 could not be had: there "equal" and "not equal" both failed
to compile, for a cause that was not found out either. That the 32 lines and the ten sizes are those
of a public file is not said here: see Johnson/Goal/PlanValues/ScopeAtPlan.lean. Nothing on
soundness.
-/
import OnBytes.Tie.Pv.KeyLookup.AdmAtPlan
import OnBytes.Plan.FromLayout
import OnBytes.Params.EntryStagesRecord
import Johnson.Top.H.KeyRangesFull
import Cb.Pv.KeyLookup.FullPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Plan

/-- The sizing of the ranges hands on the lines' lookups, message number and matrix size. -/
theorem rangesSized_lookups {s : Setting} {L : RangesLines} {codes c : Codes} {z : RangesSized}
    (h : rangesSized s L codes = some (z, c)) :
    z.x.lookups = L.lookups ∧ z.x.messageId = L.messageId ∧ z.matrix = ⟨L.kCol, L.matrixRows⟩ := by
  unfold rangesSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨last, _, h⟩ := opt_bind h
  replace h := opt_guard h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨test, ht, h⟩ := opt_bind h
  split at h
  rename_i stages codes' he
  obtain ⟨first, _, h⟩ := opt_bind h
  try extract_lets at h
  obtain ⟨ha, h⟩ := opt_guard_not h
  cases h
  exact ⟨rfl, rfl, rfl⟩

/-- The same of a key's sizes. -/
theorem keySized_lookups {l : Lines} {shape : Shape} {z : KeySized}
    (h : keySized l shape = some z) :
    ∃ L, rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart = some L ∧
      z.ranges.x.lookups = L.lookups ∧ z.ranges.x.messageId = L.messageId ∧
      z.ranges.matrix = ⟨L.kCol, L.matrixRows⟩ := by
  obtain ⟨_, L, _, _, _, hL, _, _, hR⟩ := keySized_parts h
  exact ⟨L, hL, rangesSized_lookups hR⟩

/-- The shape of the test on the table has the lines' kLo and the table's v. -/
theorem linSized_kCol {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) : x.shape.kCol = L.kLo + T.v := by
  unfold linSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨⟨x1, y1, z1⟩, _, h⟩ := opt_bind h
  replace h := opt_guard h
  obtain ⟨stU, _, h⟩ := opt_bind h
  obtain ⟨stO, h⟩ := opt_either h
  obtain ⟨stW, _, h⟩ := opt_bind h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- The sizing of a table with a record keeps its row variables. -/
theorem sizeRecordedTable_v {s : Setting} {T T' : TableSize} {a b : Nat}
    (h : sizeRecordedTable s T a b = some T') : T'.v = T.v := by
  unfold sizeRecordedTable at h
  extract_lets at h
  split at h
  · cases h
  · cases h
    rfl

/-- The table that follows from the lines has the line's row variables. -/
theorem deriveTable_v {s : Setting} {l : Lines} {T : TableSize} (h : deriveTable s l = some T) :
    T.v = l.tableRowsLog := by
  unfold deriveTable at h
  extract_lets at h
  split at h
  · cases h
  · exact (sizeRecordedTable_v h).trans rfl

/-- The matrix that the blocks of a chain take has the lines' number of column variables, where the
table has no more row variables than the shared point has coordinates. -/
theorem keySized_onceKCol {l : Lines} {shape : Shape} {z : KeySized}
    (h : keySized l shape = some z) (hb : l.tableRowsLog ≤ l.blockLog) :
    (Wf.matrixOf z.once.shape).kCol = l.blockLog := by
  obtain ⟨T, L, rows, _, hT, _, _, ho, _⟩ := keySized_parts h
  show z.once.shape.kCol = l.blockLog
  rw [linSized_kCol ho, deriveTable_v hT]
  show l.blockLog - l.tableRowsLog + l.tableRowsLog = l.blockLog
  omega

/-- The planner's three computing steps to a key's lookups: the number of column variables, the
lookups, and the number of the oracle message with the multiplicities. -/
def looksOf (l : Lines) (w : Model.WsShape) (p3 : Bool) : Option (Nat × List WfLookup × Nat) :=
  match Model.wsLayOf w p3 l.blockLog with
  | .error _ => none
  | .ok Y =>
    match shapeOfLayout Y Y.lk with
    | none => none
    | some sh =>
      (rangesLines { sh with kCol := l.blockLog } l.onceRanges l.rangesPart).map fun L =>
        (L.kCol, L.lookups, L.messageId)

/-- **What the sizing of a key returns holds these.** -/
theorem looks_of_keySized {l : Lines} {w : Model.WsShape} {p3 : Bool} {Y : Model.WsLay}
    {sh : Shape} {z : KeySized} (hY : Model.wsLayOf w p3 l.blockLog = .ok Y)
    (hs : shapeOfLayout Y Y.lk = some sh) (hz : keySized l sh = some z) :
    looksOf l w p3 = some (z.ranges.matrix.kCol, z.ranges.x.lookups, z.ranges.x.messageId) := by
  obtain ⟨L, hL, e1, e2, e3⟩ := keySized_lookups hz
  unfold looksOf
  rw [hY]
  dsimp only
  rw [hs]
  dsimp only
  rw [hL, e1, e2, e3]
  rfl

/-- The ten sizes of the model at full size on which the layout of the committed matrix depends. -/
def wsFull : Model.WsShape :=
  { D := 2048, L := 48, d := 5120, dh := 128, dkv := 1024, dq := 5120, f := 16384, fe := 8192,
    NE := 128, V := 202048 }

set_option maxRecDepth 1000000 in
/-- **The written lookups are the planner's**, at the full size's lines and sizes. -/
theorem looksOf_full : looksOf recordLines wsFull true =
    some (18, [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full], 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the planner's lookups are not the two written ones in the other order. -/
theorem looksOf_control_order : looksOf recordLines wsFull true ≠
    some (18, [Johnson.Pack.lk1Full, Johnson.Pack.lk0Full], 1) :=
  of_decide_eq_false (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- A control: at another value of the line ranges-part the planner's lookups are others. -/
theorem looksOf_control_dial : looksOf { recordLines with rangesPart := 17 } wsFull true ≠
    some (18, [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full], 1) :=
  of_decide_eq_false (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- A control: at a model of two layers the planner's lookups are others. -/
theorem looksOf_control_layers : looksOf recordLines { wsFull with L := 2 } true ≠
    some (18, [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full], 1) :=
  of_decide_eq_false (by decide +kernel)

/-- The record of a lookup reads neither the message's number nor the matrix's rows. -/
theorem pubOf_lookupOf (id : ℕ) (m : Wf.Matrix) (l : WfLookup) :
    pubOf (Wf.lookupOf id m l) = pubOf (Wf.lookupOf 0 ⟨m.kCol, 0⟩ l) := rfl

set_option maxRecDepth 1000000 in
theorem pub_lk0 : pubOf (Wf.lookupOf 0 ⟨18, 0⟩ Johnson.Pack.lk0Full) = pubFull₁ := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pub_lk1 : pubOf (Wf.lookupOf 0 ⟨18, 0⟩ Johnson.Pack.lk1Full) = pubFull₂ := by
  decide +kernel

/-- The records of the two written lookups at 18 column variables. -/
theorem pubs_of_looks {x : WfPublic} {m : Wf.Matrix} (hk : m.kCol = 18)
    (hl : x.lookups = [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full]) :
    (Wf.lookupsOf x m).map pubOf = [pubFull₁, pubFull₂] := by
  unfold Wf.lookupsOf
  rw [hl]
  show [pubOf (Wf.lookupOf x.messageId m Johnson.Pack.lk0Full),
    pubOf (Wf.lookupOf x.messageId m Johnson.Pack.lk1Full)] = _
  rw [pubOf_lookupOf, pubOf_lookupOf x.messageId m Johnson.Pack.lk1Full, hk, pub_lk0, pub_lk1]

/-- **At every key's sizes that the planner returns from the full size's lines and the layout of the
full size's ten sizes, the lookups' records are the two written ones**, in this order, at the matrix
that the blocks of a chain take and at the sizing's own; and the oracle message with the
multiplicities is number 1. -/
theorem pubs_full {Y : Model.WsLay} {sh : Shape} {z : KeySized}
    (hY : Model.wsLayOf wsFull true recordLines.blockLog = .ok Y)
    (hs : shapeOfLayout Y Y.lk = some sh) (hz : keySized recordLines sh = some z) :
    (Wf.lookupsOf z.ranges.x (Wf.matrixOf z.once.shape)).map pubOf = [pubFull₁, pubFull₂] ∧
      (Wf.lookupsOf z.ranges.x z.ranges.matrix).map pubOf = [pubFull₁, pubFull₂] ∧
      z.ranges.x.lookups = [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full] ∧
      (Wf.matrixOf z.once.shape).kCol = 18 ∧ z.ranges.matrix.kCol = 18 ∧
      z.ranges.x.messageId = 1 := by
  have h := (looks_of_keySized hY hs hz).symm.trans looksOf_full
  have h' := Option.some.inj h
  have a1 : z.ranges.matrix.kCol = 18 := congrArg Prod.fst h'
  have a2 : z.ranges.x.lookups = [Johnson.Pack.lk0Full, Johnson.Pack.lk1Full] :=
    congrArg (fun t => t.2.1) h'
  have a3 : z.ranges.x.messageId = 1 := congrArg (fun t => t.2.2) h'
  have a0 : (Wf.matrixOf z.once.shape).kCol = 18 := keySized_onceKCol hz (by decide)
  exact ⟨pubs_of_looks a0 a2, pubs_of_looks a1 a2, a2, a0, a1, a3⟩

end Lk6.AtPlan

#print axioms Lk6.AtPlan.looks_of_keySized
#print axioms Lk6.AtPlan.looksOf_full
#print axioms Lk6.AtPlan.looksOf_control_order
#print axioms Lk6.AtPlan.looksOf_control_dial
#print axioms Lk6.AtPlan.looksOf_control_layers
#print axioms Lk6.AtPlan.pub_lk0
#print axioms Lk6.AtPlan.pub_lk1
#print axioms Lk6.AtPlan.pubs_full
