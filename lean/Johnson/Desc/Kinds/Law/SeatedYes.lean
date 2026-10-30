-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SeatedYes.lean.
WHAT IT DOES NOT SHOW. No soundness. Nothing that needs a promise on the record in front: for these
see Law/SeatedSays.lean's rowPromise_seated (under K6Left). That the step goes on anywhere: not
here.
LETTERS. No "there is". ms, l: read by h alone; ft, rs, cols, n: by the step alone.
OBJECT. The block as a lot seats it (Stored/HeadAddsAtS.lean: seatedClaims W l ms): its step.
USER. A row's clause "behind the block", which should ask of the record in front only what it
spends.
WHAT IT IS. WHAT THE SEATED BLOCK's STEP GIVES BY ITS GOING ON ALONE, WITH NO PREMISE ON THE RECORD
IN
FRONT: the record's own test on the request said yes in front; no mark in front, none behind;
behind,
the two readers of the lookup's hearing agree whole; the ledger's list of arrays is as it was.
  seated_yes        the five.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SeatedSays
import Johnson.Desc.Kinds.Law.KeepsTrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes
open VerifiableInference.Desc (Block Claim OpenedColumn)
open VerifiableInference.Desc.First (S)

/-- **By the step's going on alone.** -/
theorem seated_yes {W : Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) {ft : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : Nat} (hs : b.step ft s rs cols = .ok (s', n)) :
    startOk W s = true ∧ s.failed = none ∧ s'.failed = none ∧ s'.look? = s'.lookHeard? ∧
      (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees := by
  obtain ⟨bU, hU, hsU, h4⟩ := seated_step h hs
  obtain ⟨m1, m2⟩ := Came.unmarked_both W l bU hU ft s rs cols s' n hsU
  obtain ⟨gs, hd⟩ := Came.step_decide ft bU s rs cols s' n hsU
  refine ⟨h4, m1, m2, ?_, blockOf_trees W l bU hU s s' _ gs hd⟩
  unfold blockOf at hU
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp hU
  exact Came.look_behind W.hS iU3 _ l hd

end VerifiableInference.Desc.Kinds.Head.Law
