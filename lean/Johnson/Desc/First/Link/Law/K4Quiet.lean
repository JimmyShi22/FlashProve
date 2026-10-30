-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K4Quiet.lean: THE BATCHING KIND's TWO PREMISES ON A RUN BEHIND THE
BATCHING, PAID AT THE LAYERS' KIND's RUN "free-slot", AT THE CARRIED RECORD: `QuietOk`
(Johnson/Desc/First/Batch/Law/Moves.lean) and the door's duty `KeepsDoor` (MovesDoor.lean). Three
theorems of a few lines, under ONE named premise on the shared letters (hkeep, as in K4Run.lean):
calls of `freeSlotAtS` (Johnson/Desc/First/K4/RunsAtS.lean) and of K4Run.lean's `k4_frame` and
`get_wrote`, at the ledger as it was.

  `k4_freeSlot_wrote`: where the run "free-slot" of `blockAtC p` returns e₁ from e: e stands in a
    layers' link a and `Wrote e a a.F e₁`: THE LEDGER IS AS IT WAS. IT IS NOT "THE RECORD HANDED
    BACK" TO THE LETTER: `Wrote` lays the debt of rows as K4's lens reads it: "some 0" becomes none.
  **`k4_freeSlot_quietOk`**: `QuietOk atS (O9 φ Ok Fu) (Fx9 φ Ok) run`, if a run's writing leaves φ
    (hkeep).
  **`k4_freeSlot_door`**: `KeepsDoor atS e e₁` wherever the run returns. No premise.

Limits. hkeep IS SHOWN OF NO φ. What the run TESTS (every slot below used has a coefficient in the
one equation, but the merge's) is not spent here: `freeSlotAtS_test`
(Johnson/Desc/First/K4/RunsAtC.lean) has it. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.K4Run
import Johnson.Desc.First.Batch.Law.MovesDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K4Run
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par blockAtC blockAtS Wrote Core freeSlotAtS)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S LayOwn)

/-- Where the run "free-slot" returns: the ledger is as it was. -/
theorem k4_freeSlot_wrote {p : Par} {run : S → Except String S}
    (hr : (blockAtC p).after.lookup "free-slot" = some run) {e e₁ : S} (h : run e = .ok e₁) :
    ∃ a : LayOwn, Wrote e a a.F e₁ :=
  freeSlotAtS (p := p) (show (blockAtS p).after.lookup "free-slot" = some run from hr) h

variable {α K : Type}

/-- **QuietOk OF K4's RUN "free-slot", AT THE REAL RECORD.** -/
theorem k4_freeSlot_quietOk (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Par)
    (run : S → Except String S) (hr : (blockAtC p).after.lookup "free-slot" = some run)
    (hkeep : ∀ s a G s', Wrote s a G s' → φ s' = φ s) :
    QuietOk atS (O9 (K := K) φ Ok Fu) (Fx9 φ Ok) run := by
  intro q e a9 e₁ hf hg ha hs hrun
  obtain ⟨a, hw⟩ := k4_freeSlot_wrote hr hrun
  obtain ⟨a₁, ha₁, _, _, k1, _, k3, k4, k5⟩ :=
    k4_frame φ Ok hkeep q e e₁ a9 a a.F hf hg ha hs hw (Core.refl _) (Later.refl _)
  exact ⟨a₁, ha₁, k1, k3, k4, k5⟩

/-- **The door's duty of K4's run "free-slot".** -/
theorem k4_freeSlot_door (p : Par) (run : S → Except String S)
    (hr : (blockAtC p).after.lookup "free-slot" = some run) :
    ∀ e e₁, run e = .ok e₁ → KeepsDoor atS e e₁ := by
  intro e e₁ h a9 ha
  obtain ⟨a, hw⟩ := k4_freeSlot_wrote hr h
  obtain ⟨a₁, ha₁, _, f2, f3, _⟩ := get_wrote e e₁ a9 ha a a.F hw
  exact ⟨a₁, ha₁, by rw [f2], f3⟩

end VerifiableInference.Desc.K4Run

#print axioms VerifiableInference.Desc.K4Run.k4_freeSlot_quietOk
#print axioms VerifiableInference.Desc.K4Run.k4_freeSlot_door
