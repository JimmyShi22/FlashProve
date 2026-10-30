-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FormsOpenFull.lean: THE KIND K1's SHARES AT THE ITEMS "forms m
piece run", AT THE 25 READS' MEMBERS: THE PREMISE hi OF exchangeAtS_forms
(Honest/K1/Law/FormsShare.lean): THE ITEM formsT l j n IS OPEN IN FRONT OF THE READS' MEMBER OF
SEGMENT l, AT EACH RUN OF THE TABLE's ROW. PUBLIC DATA ALONE: the table's two written lists. Three
theorems; no definition.

  - formsT_open_full   A CLOSED TEST ON THE TWO WRITTEN LISTS (P5J.At.links, P5J.At.ps), by
                  evaluation in Lean's kernel: at each l < 25 and each (j, n) of earlyRuns (subAt l)
                  the item formsT l j n stands in the thread's forward open set (fwdOpen,
                  Honest/Thread/Thr.lean) at the border K1.noL l false: 101 items.
  - formsT_open_no   A CONTROL: one border further, behind the reads' member, the same test says no
                  at every one of the 101: the member's row has shut them.
  - formsT_open   the first as a sentence. AT ProofFile's lettersHead IT IS hi: there thread.opened b is
                  fwdOpen (start L.links) (FirstRows.rows L.links L.ps) b, and L.links, L.ps are
                  these two lists, by unfolding.

THE PATTERN IS ANOTHER HOUSE's: part 1's worth_open_full and worth_open_no (Honest/K8/
WorthTwoOfOpen.lean): the like test at two other items, at the 25 batchings' borders. ANOTHER ROAD
TO hi, NOT TAKEN: "what a row shuts is open before it" under the test fwdFit (the lookups'
asked_of_fit; ProofFile's fwdFit_of_opens): its closed test at these lists stands over a file that is on
no seal and on no booked row.

Limits. THE FULL SIZE's TWO LISTS ALONE. Evaluations in Lean's kernel (decide +kernel): no compiled
code. Nothing on what any item says. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.K1.Law.LaterOne
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item earlyRuns start)

/-- **EACH OF THE 101 IS OPEN IN FRONT OF ITS READS' MEMBER.** -/
theorem formsT_open_full : ((List.range 25).all fun l =>
    (earlyRuns (IM.subAt l)).all fun x =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
        (K1.noL l false)).contains (Item.formsT l x.1 x.2)) = true := by
  decide +kernel

/-- A control: one border further none of the 101 is open. -/
theorem formsT_open_no : ((List.range 25).any fun l =>
    (earlyRuns (IM.subAt l)).any fun x =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
        (K1.noL l false + 1)).contains (Item.formsT l x.1 x.2)) = false := by
  decide +kernel

/-- **THE PREMISE hi**, at the two written lists. -/
theorem formsT_open {l : ℕ} (hl : l < 25) {j : ℕ} {n : String}
    (h : (j, n) ∈ earlyRuns (IM.subAt l)) :
    Item.formsT l j n ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (K1.noL l false) := by
  have hb := List.all_eq_true.1 (List.all_eq_true.1 formsT_open_full l (List.mem_range.2 hl))
    (j, n) h
  simpa using hb

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.formsT_open_full
#print axioms ProofFile.Honest.K1.formsT_open_no
#print axioms ProofFile.Honest.K1.formsT_open
