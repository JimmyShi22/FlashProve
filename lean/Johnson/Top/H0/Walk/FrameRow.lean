-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameRow.lean: the pending row that "cleared" will lay, as a plain function of
the carried record, with a public Bool that says whether the record holds one; and the law that
"cleared" lays just that row at the pile's end.

  leftOf        what the open link's sub-proof has left for its row: at a layers' link leftLay
                (Johnson/Desc/First/Walk/Frame.lean), at the head's link leftHead
                (Johnson/Desc/First/Close/TailHead.lean); none elsewhere
  rowAt         the reader: the row that pendingRowO (Johnson/Desc/First/Pend/Row.lean) makes of
                what is left, at the record's own number of the index masks' message and its own
                messages; none where nothing is left or that function refuses
  hasRow        the public Bool: rowAt is some
  rowAt_some    what a some of rowAt says, both ways
  cleared_lays  where the link's record leaves a row, a yes of clearWith at pendingRowO gives: the
                record in front holds a row, and the pile behind is the pile in front with that
                row at its end
  cleared_lays_none   where it leaves none: the pile is the pile in front
  clearedLay_lays, tailHead_lays   the two at the texts that run: a layers' link's clear and the
                head's link's end, at the one reader leftOf

Limits. The reader reads the ledger of the index masks' message AT THE RECORD AT WHICH IT IS ASKED:
the mask entry that the row bears is that ledger's next free one. So rowAt at a border further in
front is the row that "cleared" lays only if no block between takes an entry of that ledger, turns
the message's number or turns what is left: that is those blocks' laws' to say; nothing here says
it. n, lay and lin are letters. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Desc.First.Close.TailHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.Close (leftHead countsHead tailHead)

/-- What the open link's sub-proof has left for its row. -/
def leftOf (s : S) : Option WsForkOut :=
  match leftLay s with
  | some w => some w
  | none => leftHead s

/-- The reader, at any "left". n: the plan's number of the sub-proof's claims on the weights. -/
def rowBy (left : S → Option WsForkOut) (lay : WsLay) (n : Nat) (lin : Params.LinShape) (s : S) :
    Option TensorRow :=
  (left s).bind fun w => (pendingRowO lay s.out.indexMasks w n lin s.st.oracles).toOption.map (·.1)

/-- **The pending row that "cleared" will lay.** -/
def rowAt (lay : WsLay) (n : Nat) (lin : Params.LinShape) (s : S) : Option TensorRow :=
  rowBy leftOf lay n lin s

/-- **The record holds a pending row.** -/
def hasRow (lay : WsLay) (n : Nat) (lin : Params.LinShape) (s : S) : Bool :=
  (rowAt lay n lin s).isSome

theorem rowBy_some {left : S → Option WsForkOut} {lay : WsLay} {n : Nat} {lin : Params.LinShape}
    {s : S} {r : TensorRow} :
    rowBy left lay n lin s = some r ↔
      ∃ w os, left s = some w ∧
        pendingRowO lay s.out.indexMasks w n lin s.st.oracles = .ok (r, os) := by
  unfold rowBy
  cases hl : left s with
  | none => simp
  | some w =>
    cases hp : pendingRowO lay s.out.indexMasks w n lin s.st.oracles with
    | error e => simp [Except.toOption, hp]
    | ok p => obtain ⟨q, os⟩ := p; simp [Except.toOption, hp]

theorem rowAt_some {lay : WsLay} {n : Nat} {lin : Params.LinShape} {s : S} {r : TensorRow} :
    rowAt lay n lin s = some r ↔
      ∃ w os, leftOf s = some w ∧
        pendingRowO lay s.out.indexMasks w n lin s.st.oracles = .ok (r, os) := rowBy_some

/-- **Where the link leaves a row: "cleared" lays the reader's row at the pile's end.** -/
theorem cleared_lays {X : LinkPub} {counts : S → Except String Unit} {left : S → Option WsForkOut}
    {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) :
    ∃ r, rowBy left lay X.NCL lin s = some r ∧ t.out.pending = s.out.pending ++ [r] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hrow⟩ := clearWith_ok h
  obtain ⟨w, r, os, hw, hr, hout, _⟩ := hrow hv
  exact ⟨r, rowBy_some.2 ⟨w, os, hw, hr⟩, by rw [hout]; rfl⟩

/-- Where it leaves none: the pile is the pile in front. -/
theorem cleared_lays_none {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) (hv : X.fv = false) :
    t.out.pending = s.out.pending := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h0, _⟩ := clearWith_ok h
  rw [(h0 hv).1]

theorem leftOf_of_lay {s : S} {w : WsForkOut} (h : leftLay s = some w) : leftOf s = some w := by
  simp [leftOf, h]

theorem leftOf_of_head {s : S} {w : WsForkOut} (h : leftHead s = some w) : leftOf s = some w := by
  unfold leftHead at h
  unfold leftOf leftLay leftHead
  cases hh : s.here <;> simp_all

/-- At a layers' link's clear, at the one reader. -/
theorem clearedLay_lays {X : LinkPub} {counts : S → Except String Unit} {lay : WsLay}
    {lin : Params.LinShape} {s t : S}
    (h : clearWith X counts leftLay (fun im w n os => pendingRowO lay im w n lin os) s = .ok t)
    (hv : X.fv = true) :
    hasRow lay X.NCL lin s = true ∧
      ∃ r, rowAt lay X.NCL lin s = some r ∧ t.out.pending = s.out.pending ++ [r] := by
  obtain ⟨r, hr, hp⟩ := cleared_lays h hv
  obtain ⟨w, os, hw, hq⟩ := rowBy_some.1 hr
  have e : rowAt lay X.NCL lin s = some r := rowAt_some.2 ⟨w, os, leftOf_of_lay hw, hq⟩
  exact ⟨by simp [hasRow, e], r, e, hp⟩

/-- At the head's link's end, at the one reader. -/
theorem tailHead_lays {X : LinkPub} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : tailHead X lay lin s = .ok t) (hv : X.fv = true) :
    hasRow lay X.NCL lin s = true ∧
      ∃ r, rowAt lay X.NCL lin s = some r ∧ t.out.pending = s.out.pending ++ [r] := by
  obtain ⟨r, hr, hp⟩ := cleared_lays (left := leftHead) h hv
  obtain ⟨w, os, hw, hq⟩ := rowBy_some.1 hr
  have e : rowAt lay X.NCL lin s = some r := rowAt_some.2 ⟨w, os, leftOf_of_head hw, hq⟩
  exact ⟨by simp [hasRow, e], r, e, hp⟩

#print axioms rowBy_some
#print axioms rowAt_some
#print axioms cleared_lays
#print axioms cleared_lays_none
#print axioms clearedLay_lays
#print axioms tailHead_lays

end Johnson.Desc.First.Walk.Law
