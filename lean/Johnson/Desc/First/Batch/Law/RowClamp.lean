-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/RowClamp.lean: THE SENTENCE ON THE SEGMENT's ONE EQUATION's ROW
(`rowEqQ`, CoresTable.lean) AT THE CLAMPED READER `LinkJoin.rdC cs arr ms w`
(Johnson/Desc/First/Link/Law/ClampPin.lean: each member's typed message read back as a table, 0
outside its ranges) AND AT `seatTab cs arr ms w`, at which the composed meaning states it, HAS ONE
TRUTH VALUE, UNDER ONE NAMED PREMISE ON THE STATE's LAST ROW AND THE LIST OF MEMBERS. The sibling,
for this sentence, of the five of Johnson/Desc/Sound/Clamp/FormsClamp.lean. A definition and
theorems.
  `RowInside cs ms own a N row`: every entry of a table of the oracle messages 0, .., N - 1 on which
    the row has a weight other than 0 lies inside the ranges of the member that sits at its seat.
  `part_clamp`, `rowSum_clamp`: under it the row's sum (`rowSum`, AsRow.lean) is the same at both
    readers: where the weight is 0 the entry is not read; elsewhere by `tabQ_clamp`
    (Johnson/Desc/Sound/Clamp/TabClamp.lean).
  `rowEqQ_clamp`: **an "if and only if"**, where the row that stands last in the segment's group is
    so.
Limits. `RowInside` IS SHOWN AT NO STATE HERE. What it wants: that the last row is the one that the
one equation's step has made (`asRow_coef`, AsRow.lean: its weights on a main table are sums of the
terms' shares; on a mask table they stand at the segment's mask row's entries below the number of
the equation's coefficients, and nowhere else), and `InsideAt` (FormsClamp.lean) at the part in
front. THE SUM RUNS OVER THE STATEMENT's 2 ^ (row bits + place bits) ENTRIES: more than a member's
rows: at a row with a weight there the two readers may part. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.CoresTable
import Johnson.Desc.Sound.Clamp.TabClamp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (rdC)

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (own : List (ℕ × ℕ))

/-- **Every entry of a table on which the row has a weight other than 0 lies inside the ranges of
the member at its seat.** -/
def RowInside (a : K9.Part) (N : ℕ) (row : OnBytes.Row) : Prop :=
  ∀ o < N, ∀ (part : OnBytes.Part) (J : ℕ),
    J < 2 ^ (a.d.st.rowBits o part + a.d.st.placeBits o part) →
    Reading.gl.val (row.coefficient o part J) ≠ 0 → ∀ x y, K9.seatAt own a.d.book o = some x →
    (ms.find? fun y => decide (seatOf y = x)) = some y →
    InMsg cs (y.1.l.get y.2).1 (part == .mask) (J % 2 ^ a.d.st.rowBits o part)
      (J / 2 ^ a.d.st.rowBits o part)

/-- One table's share of the row's sum is the same at both readers. -/
theorem part_clamp (w : Wit Cells Tok MsgT) (a : K9.Part) (N : ℕ) (row : OnBytes.Row)
    (h : RowInside cs ms own a N row) (o : ℕ) (ho : o < N) (part : OnBytes.Part) :
    (∑ J ∈ Finset.range (2 ^ (a.d.st.rowBits o part + a.d.st.placeBits o part)),
        Reading.gl.val (row.coefficient o part J) *
          tabQ own a.d.st a.d.book (rdC cs arr ms w) o part J) =
      ∑ J ∈ Finset.range (2 ^ (a.d.st.rowBits o part + a.d.st.placeBits o part)),
        Reading.gl.val (row.coefficient o part J) *
          tabQ own a.d.st a.d.book (seatTab cs arr ms w) o part J := by
  refine Finset.sum_congr rfl fun J hJ => ?_
  by_cases hz : Reading.gl.val (row.coefficient o part J) = 0
  · rw [hz, zero_mul, zero_mul]
  · rw [tabQ_clamp cs arr ms own a.d.st a.d.book w o J part
      (h o ho part J (Finset.mem_range.1 hJ) hz)]

/-- **The row's sum is the same at both readers.** -/
theorem rowSum_clamp (w : Wit Cells Tok MsgT) (a : K9.Part) (N : ℕ) (row : OnBytes.Row)
    (h : RowInside cs ms own a N row) :
    rowSum Reading.gl a.d.st N (tabQ own a.d.st a.d.book (rdC cs arr ms w)) row =
      rowSum Reading.gl a.d.st N (tabQ own a.d.st a.d.book (seatTab cs arr ms w)) row := by
  unfold rowSum
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [part_clamp cs arr ms own w a N row h o (Finset.mem_range.1 ho) .main,
    part_clamp cs arr ms own w a N row h o (Finset.mem_range.1 ho) .mask]

/-- **THE ONE EQUATION's ROW AT THE CLAMPED READER IS THE COMPOSED MEANING's OWN.** -/
theorem rowEqQ_clamp (N : ℕ) (s : S) (w : Wit Cells Tok MsgT)
    (h : ∀ a G row, atS.get? s = some a → a.d.st.groups[a.L.check.group]? = some G →
      G.rows.back? = some row → RowInside cs ms own a N row) :
    rowEqQ own N s (rdC cs arr ms w) ↔ rowEqQ own N s (seatTab cs arr ms w) := by
  unfold rowEqQ LastRowAt
  refine forall_congr' fun a => forall_congr' fun ha => forall_congr' fun G =>
    forall_congr' fun hG => forall_congr' fun row => forall_congr' fun hr => ?_
  have e : ∀ rd, tabAt own rd s = tabQ own a.d.st a.d.book rd := fun rd => by
    unfold tabAt
    rw [ha]
  rw [e, e, rowSum_clamp cs arr ms own w a N row (h a G row ha hG hr)]

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.rowSum_clamp
#print axioms VerifiableInference.Desc.K9L.rowEqQ_clamp
