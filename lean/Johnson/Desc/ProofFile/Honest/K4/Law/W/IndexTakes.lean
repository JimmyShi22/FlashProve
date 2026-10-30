-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IndexTakes.lean: CONDITIONAL where h stands. Closed facts,
and statements with their proofs.

What is here. HOW MANY ENTRIES OF THE INDEX MASKS' MESSAGE ARE TAKEN IN FRONT OF A SEGMENT, AS
NUMERALS. Under the library's hypothesis on the public files the planner's flags count as the
written ones do (`takes_written`: the library's `P1L20.rowsBefore_scope`,
Johnson/P1L20R/RoomFold.lean); of the written list's first 2 g segments just g leave a pending row,
and of the first 24 twelve (by Lean's kernel). IT IMPORTS FILES OF THE LIBRARY ALONE, AND NO FILE
OF ANY KIND's LAWS: so that other kinds' files can call it.

  `bearing_even`, `bearing_head`   **BY THE KERNEL**: of the written list's first 2 g segments g
      leave a row, at g below 12; of the first 24, twelve.
  `bearing_even_off`   A NEGATIVE TEST THAT COULD FAIL: of the first two segments not two leave a
      row.
  `takes_written`   the planner's flags count as the written ones do, below segment 25, under h.
  `indexTakes_head`   in front of the output head's segment, number 24, twelve entries are taken,
      under h.

Not shown here. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). THE FULL SIZE ALONE, and the format's second hash function alone. THREE
CLOSED FACTS by evaluation in Lean's kernel, which no independent checker has replayed; the list of
segments in them is written. NOTHING ON WHO TAKES WHICH ENTRY: numbers alone. A program's walk
from import to import, which reads import lines alone and stops unopened at Johnson/Goal/,
ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 43 modules under Johnson/Goal/
and at 6 under Johnson/Bridge/: so these counts are lower bounds; it met no module under ThirdParty/
or Johnson/D/ and none that begins Cb.Bridge. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one. Nothing on soundness, on completeness or on any other
property.

No property is claimed.
-/
import Johnson.P1L20R.RoomFold
import Johnson.P5J.FoldJ1
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (FillP1.fvsAt)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open P5J (AtMgA TS)

/-! ## 1 Closed facts -/

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: of the written list's first 2 g segments just g leave a pending row. -/
theorem bearing_even : ∀ g, g < 12 → rowsBefore P1L20.bearingList (2 * g) = g := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: of the first 24 segments twelve leave a pending row. -/
theorem bearing_head : rowsBefore P1L20.bearingList 24 = 12 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test that could fail**: of the first two segments not two leave a row. -/
theorem bearing_even_off : decide (rowsBefore P1L20.bearingList 2 = 2) = false := by
  decide +kernel

/-! ## 2 Under the library's hypothesis -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- The planner's flags count as the written ones do. CONDITIONAL on h and hm. -/
theorem takes_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {m : ℕ} (hm : m < 25) :
    rowsBefore (FillP1.fvsAt Zp) m = rowsBefore P1L20.bearingList m := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P1L20.rowsBefore_scope h.scope h.reads O (P5J.flat_ok h.toAtMg) hm

/-- In front of the output head's segment twelve entries are taken. CONDITIONAL on h. -/
theorem indexTakes_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    rowsBefore (FillP1.fvsAt Zp) 24 = 12 := by
  rw [takes_written h (by omega)]
  exact bearing_head

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.bearing_even
#print axioms ProofFile.Honest.K4.W.bearing_head
#print axioms ProofFile.Honest.K4.W.bearing_even_off
#print axioms ProofFile.Honest.K4.W.takes_written
#print axioms ProofFile.Honest.K4.W.indexTakes_head
