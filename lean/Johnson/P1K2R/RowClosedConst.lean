-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/RowClosedConst.lean: the code switch: FOUR CLOSED FACTS ON THE TYPED STRUCTURE THAT
THE KIND's NAMED CONDITION ASKS (`K2AllOwes`: the letter h and the fields hW, hz, ht), AT AN ENTRY
OF THE WRITTEN TABLE OF THE FULL SIZE. A gathering: all four lie in the library, by
Lean's kernel: three with a test that it can fail (`tableFullLit_ok` · `full_written_ok` ·
`full_sized`; `full_can_fail` · `full_written_can_fail` · `sized_can_fail`), and `target_full`
    (At128.lean).

Main names:
  `target_other`: a negative test beside the library's `target_full`: at 127 the sentence fails.
  `row_closed`: at an entry r of the written table: `r.ok`, `r.writtenOK`, `r.sizedB` accept and
    `r.set.target = 128`.
Limits. Written numbers: those of LitRows.lean. That the made table is the written one is another
file's named test. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenLitFull
import Johnson.Top.H0.K2Caller.LitFull
import Johnson.Top.H0.K2Caller.SizedLit
import Johnson.Top.H0.K2Caller.At128

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller

/-- A negative test. -/
theorem target_other : (tableFullLit.all fun r => decide (r.set.target = 127)) = false := by
  decide +kernel

/-- **The four closed facts at an entry of the written table.** -/
theorem row_closed {m : ℕ} {r : SwRow} (hr : tableFullLit[m]? = some r) :
    r.ok = true ∧ r.writtenOK = true ∧ r.sizedB = true ∧ r.set.target = 128 := by
  have hm : r ∈ tableFullLit := List.mem_of_getElem? hr
  exact ⟨List.all_eq_true.1 tableFullLit_ok r hm, List.all_eq_true.1 full_written_ok r hm,
    List.all_eq_true.1 full_sized r hm, target_full r hm⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.target_full
#print axioms VerifiableInference.Desc.First.K2Caller.target_other
#print axioms VerifiableInference.Desc.First.K2Caller.row_closed
#print axioms VerifiableInference.Desc.First.K2Caller.tableFullLit_ok
#print axioms VerifiableInference.Desc.First.K2Caller.full_written_ok
#print axioms VerifiableInference.Desc.First.K2Caller.full_sized
