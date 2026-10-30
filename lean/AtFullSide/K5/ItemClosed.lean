-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K5/ItemClosed.lean: one closed fact, with three controls: at the stored full-size public files the clause on
the request's item, in the letters of ItemLetters.lean and at the list form of the format's second hash function, says yes.
Decided by evaluation in Lean's kernel.

  clause_closed        clauseBy olderKF 4104 id = true
  clause_short_no      a control: at a number one word short for the request's size: false (by the text no item is
                       made there)
  clause_bent_no       a control: with attention's digest laid in the place of the layers' the comparison says no
  clause_bentH_no      a control: with the layers' digest laid in the place of the head's it says no

How. "String.splitOn" does not reduce in the kernel: the texts that call it are unfolded and rewritten by splitOn_eq
(Johnson/Unfolds/SplitOn.lean), as that file's head says; then the kernel decides.

Limits. One example, at written values: VerifierAndGoals.storedPublicFiles and a request of 4,104 zero bytes. Checked by Lean's own kernel
alone. What the yes is worth is said in ItemAtFull.lean. A raised limit: «set_option maxRecDepth 1000000»: it bears on
the elaborator's depth of recursion, not on the kernel's verdict. In our trials the closed fact took the kernel about
a minute and some 18 GB of memory; whoever builds this file pays the like for each theorem that reaches the comparison.
No property of the protocol is claimed: nothing on soundness, completeness or what anything reveals.
-/
import AtFullSide.K5.ItemLetters
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFullSide.K5.Item
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.Unfolds

/-- **At the stored full-size files the clause on the request's item says yes**, at the list form of the hash. -/
theorem clause_closed : clauseBy olderKF 4104 id = true := by
  unfold clauseBy itemBy Fmt.requestItemOf Fmt.ReqLines.words heldBy namesHeld
  simp only [splitOn_eq]
  decide +kernel

/-- A control: at a number one word short for the request's size the yes or no is no; by the text no item is made
there. -/
theorem clause_short_no : clauseBy olderKF 4100 id = false := by
  unfold clauseBy itemBy Fmt.requestItemOf Fmt.ReqLines.words heldBy namesHeld
  simp only [splitOn_eq]
  decide +kernel

/-- A control: with attention's digest in the place of the layers' the comparison says no. -/
theorem clause_bent_no : clauseBy olderKF 4104 (fun d => { d with hCalls := d.hCallsA }) = false := by
  unfold clauseBy itemBy Fmt.requestItemOf Fmt.ReqLines.words heldBy namesHeld
  simp only [splitOn_eq]
  decide +kernel

/-- A control: with the layers' digest in the place of the head's the comparison says no. -/
theorem clause_bentH_no : clauseBy olderKF 4104 (fun d => { d with hCallsH := d.hCalls }) = false := by
  unfold clauseBy itemBy Fmt.requestItemOf Fmt.ReqLines.words heldBy namesHeld
  simp only [splitOn_eq]
  decide +kernel

end AtFullSide.K5.Item

#print axioms AtFullSide.K5.Item.clause_closed
#print axioms AtFullSide.K5.Item.clause_short_no
#print axioms AtFullSide.K5.Item.clause_bent_no
#print axioms AtFullSide.K5.Item.clause_bentH_no
