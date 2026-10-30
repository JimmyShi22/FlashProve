-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/No/Decl1Short.lean: A NEGATIVE LINE THAT PRESSES ON WHAT THE THREE LINES
`roundsDeclaredByBlocks.i == plans.i` AT THE WRITTEN DESCRIPTION `WP` HANG ON (Johnson/AtFull/ProofPlan/At/Decl1.lean,
Decl2.lean, Decl3.lean). One closed fact, by an evaluation in Lean's kernel, alone in its file. Two
limits are raised for it: maxRecDepth to 1000000; maxHeartbeats is lifted.

WHAT THE THREE POSITIVE LINES HOLD, AND NO MORE, BY READING: NO THEOREM HERE SAYS SO. `wOf`
(Johnson/AtFull/ProofPlan/WrittenDesc.lean) lays plans := R, and its blocks' rounds are that same R,
cut by the rows' numbers of rounds and laid in a row again. So at `WP` the test of the declared
rounds against the plan's says yes just if the rows' numbers of rounds add up to at least the list's
length. No round's content is compared with anything but itself. The negative lines
At/No/Decl1.lean, Decl2.lean and Decl3.lean bend the other side: they empty the plan's list. The
line below shows one case of the "only if".

Here the rows' numbers add up to one less. `wpSeal` (Johnson/AtFull/ProofPlan/At/Bent.lean) is `WP`
with the first chain's last row declaring no round for one. The written rows' numbers add up to
48293 (`cut_rounds`, Johnson/Desc/Ok/PlanWritten/CutTestLaws.lean), which is the list's length
(`decl_lengths`, Johnson/AtFull/ProofPlan/WP.lean); so, by arithmetic on these two, 48292 here. The
test says no.

Whence. Added at a reader's request.

Limits. A fact on a made-up value. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Bent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan

open VerifiableInference.Desc
open P2Law.ProofPlan (wpSeal)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem decl₁_short_no : (wpSeal.roundsDeclaredByBlocks.1 == wpSeal.plans.1) = false := by decide +kernel

end Johnson.AtFull.ProofPlan

#print axioms Johnson.AtFull.ProofPlan.decl₁_short_no
