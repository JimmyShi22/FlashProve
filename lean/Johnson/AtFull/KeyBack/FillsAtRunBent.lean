-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FillsAtRunBent.lean: `fills_run` (FillsAtRun.lean) with a value bent, twice.
Tests of the test: each shows that the test says no where it should.

  `fills_run_bent_count`: a tree of the shared chain is left out. The whole test says no.
  `bentA`, `bent_opened_no`, `bent_opened_rest`: the first chain gets a seventh tree that no list
    names. A no of the whole test would not tell which of its seven clauses says no. So there are
    two statements at these trees: the seventh clause (every tree is opened) says no; the six
    others, joined as `fillsB` joins them, say yes.

By evaluations in Lean's kernel (`decide +kernel`).

Limits. Nothing follows from these for any key file. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillsAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- A tree of the shared chain left out: the test says no. -/
theorem fills_run_bent_count :
    fillsB 4 10 5 keyFull.once.shape runA runB.dropLast runC = false := by
  decide +kernel

/-- The first chain's trees, and a seventh that no list names. -/
def bentA : List (Sent × Nat) := runA ++ [(⟨0, 0, 0, 0, .ownMask⟩, 6)]

set_option maxRecDepth 1000000 in
/-- At these trees the seventh clause says no. -/
theorem bent_opened_no :
    allOpened bentA runB runC ((noStored (onceOpens bentA)).flatMap (·.1))
      ((sharedOpens keyFull.once.shape runB).flatMap (·.1))
      ((noStored (secondOpens keyFull.once.shape (fun t => t.tag == .indexMask) bentA runB
        runC)).flatMap (·.1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At these trees the six other clauses say yes. -/
theorem bent_opened_rest :
    (4 == (noStored (onceOpens bentA)).length &&
      10 == (sharedOpens keyFull.once.shape runB).length &&
      5 == (noStored (secondOpens keyFull.once.shape (fun t => t.tag == .indexMask) bentA runB
        runC)).length &&
      noneBare (noStored (onceOpens bentA)) &&
      noneBare (sharedOpens keyFull.once.shape runB) &&
      noneBare (noStored (secondOpens keyFull.once.shape (fun t => t.tag == .indexMask) bentA runB
        runC))) = true := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.fills_run_bent_count
#print axioms Johnson.AtFull.KeyBack.bent_opened_no
#print axioms Johnson.AtFull.KeyBack.bent_opened_rest
