-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysLink.lean.
Three routines of a link (OnBytes/Model/Trees.lean) stay on the view: LinkM.call, rootInH, t2Batch.

One statement a routine: `DryS` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) or, for a routine of a
link, `DryL`: from every state, a run on a view that returns is still on the view (`Dry`,
OnBytes/Tie/Pv/Lookup/Ends/FoChan.lean: the mark of the dry run, false before, is false behind).
Nothing is said of a run that refuses, or of what a run reads. Where a routine takes routines or
blocks as arguments, the statement stands under the same of these. rootInH and t2Batch are proved by
the tactic `stays` (OnBytes/Tie/Pv/Lookup/Ends/FoStay.lean) on the routine's own body; LinkM.call by
the rules for bind, by hand, under the same of the block that it takes.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysLook
import OnBytes.Model.Trees

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem DryL.call (f : ChainCheck → Blk ChainCheck) (hf : ∀ k, Dry (f k)) :
    DryL (LinkM.call f) := by
  intro Lc
  show DryS (SubM.must _ >>= fun _ => (_root_.liftM (f Lc.check) : SubM ChainCheck) >>= fun check =>
    Pure.pure ((), { Lc with check := check }))
  exact (DryS.must _).bind fun _ => (DryS.lift (hf _)).bind fun _ => DryS.pure _

macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible apply DryL.call)

theorem DryL.rootInH (trees : List ℕ) : DryL (rootInH trees) := by stays
theorem DryL.t2Batch (used : ℕ) : DryL (t2Batch used) := by stays

end Fo
