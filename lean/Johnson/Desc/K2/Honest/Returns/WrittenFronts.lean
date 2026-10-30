-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/WrittenFronts.lean: AT EACH OF THE 25 WRITTEN FRONTS OF THE FULL SIZE
(`fxAt r`, Johnson/G/SwitchFrontMember.lean, r an entry of `tableFullLit`) FOUR CLAUSES OF THE LAW
"THE KIND's OWN DECISION SAYS YES" HOLD: the program's test on the target says yes
(`FrontCore.check`) · the kept old messages have the old main code (`OldFits.keptCode`) · the count
of kept rows is the sum of their main rows (`OldFits.rows`) · their main tables have at most 63
index bits (`TablesFit.bitsKept`). A test with code, Lean's kernel's yes at the table's five
different entries, and what the yes says.

  `keptFitB S old T` the last three clauses as a test
  `keptFit_says` what its yes says, each clause in its structure's own letters
  `writtenB r` the target's test and `keptFitB`, at `fxAt r`
  `writtenB_full` yes at all 25 entries
  `writtenB_can_fail` each of the two tests says no somewhere: the target's at a mask code that is
                    not in the list; `keptFitB` at another old main code: that bites its clause on
                    the code; its clauses on the rows' sum and on the bound 63 are shown no failing
                    case
  `written_at` the four clauses at an entry of the table

THE DEVICE. `writtenB_full` and `writtenB_can_fail` are closed by `decide +kernel`, six times in
all, under `set_option maxRecDepth 1000000`: as the library's own tests on this table are
(`fitB_full`, Johnson/G/SwitchFitLit.lean; `frontTests_full`, Johnson/G/SwitchFrontTests.lean). The
25 entries are five different ones (`full_all`, Johnson/Top/H0/K2Caller/LitRows.lean).

A near relative, not called: `fitB_full`: the target's test at the same target and at another
writing of the statement and of the claim in front (`stAt r`, `oldAt r`).

Limits. WRITTEN FRONTS: made of a table, not of a run; who ties a run's front to one of them is not
said here (Returns/PinReached.lean). The full size alone. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.G.SwitchFrontMember

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open Johnson.G (fxAt)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit full_all full0)

/-- Three clauses on the kept old messages' shapes, as a test. -/
def keptFitB (S : Statement) (old : SingleRows) (T : SwitchTarget) : Bool :=
  old.keptRows == ((sizesAt S old T).kept.map (·.mainRows)).sum &&
    (sizesAt S old T).kept.all fun s => s.code == old.code &&
      decide (ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll ≤ 63)

theorem keptFit_says {S : Statement} {old : SingleRows} {T : SwitchTarget}
    (h : keptFitB S old T = true) :
    (∀ o ∈ (switchKept old).toList, (S.oracles.getD o default).shape.code = old.code) ∧
      old.keptRows =
        ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape.mainRows).sum ∧
      ∀ s ∈ (sizesAt S old T).kept,
        ceilLog2 s.mainRows + (S.codes.base.getD old.code default).logEll ≤ 63 := by
  unfold keptFitB at h
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun o ho => ?_, ?_, fun s hs => (h2 s hs).2⟩
  · have hm : (S.oracles.getD o default).shape ∈ (sizesAt S old T).kept := by
      show _ ∈ (switchKept old).toList.map _
      exact List.mem_map.2 ⟨o, ho, rfl⟩
    exact (h2 _ hm).1
  · rw [h1]
    show (((switchKept old).toList.map fun o => (S.oracles.getD o default).shape).map
      (·.mainRows)).sum = _
    rw [List.map_map]
    rfl

/-- **The test at a written front.** -/
def writtenB (r : SwRow) : Bool :=
  switchTargetCheck (fxAt r).st (fxAt r).f.rows (fxAt r).T &&
    keptFitB (fxAt r).st (fxAt r).f.rows (fxAt r).T

set_option maxRecDepth 1000000 in
/-- **Lean's kernel says yes at all 25 entries of the full table.** -/
theorem writtenB_full : (tableFullLit.all writtenB) = true :=
  full_all _ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 1000000 in
/-- **Each of the two tests can fail.** The second no is one because the first entry's front has a
kept member: over no kept member `keptFitB`'s clause on the code says yes. -/
theorem writtenB_can_fail :
    switchTargetCheck (fxAt full0).st { (fxAt full0).f.rows with maskCode := 1000 }
        (fxAt full0).T = false ∧
      keptFitB (fxAt full0).st
        { (fxAt full0).f.rows with code := (fxAt full0).f.rows.code + 1 } (fxAt full0).T =
        false := by
  decide +kernel

/-- **The four clauses at an entry of the table.** -/
theorem written_at {r : SwRow} (hr : r ∈ tableFullLit) :
    switchTargetCheck (fxAt r).st (fxAt r).f.rows (fxAt r).T = true ∧
      (∀ o ∈ (switchKept (fxAt r).f.rows).toList,
        ((fxAt r).st.oracles.getD o default).shape.code = (fxAt r).f.rows.code) ∧
      (fxAt r).f.rows.keptRows = ((switchKept (fxAt r).f.rows).toList.map fun o =>
        ((fxAt r).st.oracles.getD o default).shape.mainRows).sum ∧
      ∀ s ∈ (sizesAt (fxAt r).st (fxAt r).f.rows (fxAt r).T).kept, ceilLog2 s.mainRows +
        ((fxAt r).st.codes.base.getD (fxAt r).f.rows.code default).logEll ≤ 63 := by
  have h := List.all_eq_true.1 writtenB_full r hr
  unfold writtenB at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, keptFit_says h.2⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.keptFit_says
#print axioms VerifiableInference.Desc.K2.Honest.Returns.writtenB_full
#print axioms VerifiableInference.Desc.K2.Honest.Returns.writtenB_can_fail
#print axioms VerifiableInference.Desc.K2.Honest.Returns.written_at
