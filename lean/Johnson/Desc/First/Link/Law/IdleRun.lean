-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/IdleRun.lean: A RUN OF CLAIMS THAT RETURNS NO CLAIM AND HANDS THE RECORD
BACK MEETS THE BATCHING KIND's PREMISE ON A RUN, AT ALL LETTERS, UNDER NO PREMISE. Three small
theorems over StillRun.lean. The lookup's run «guests» is such a run wherever no guest is seated.

Limits. Tools. That a run of the protocol is idle is its kind's law's to show. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.StillRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.StillRun
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)

variable {α K : Type}

/-- No form. -/
def fsNone : α × Option Pub9 → Option (List Aff) := fun _ => some []

/-- The run returns no claim and hands the record back. -/
def Idle (run : ℕ → S → Except String (List Claim × S)) : Prop := ∀ n s, run n s = .ok ([], s)

theorem idle_still (φ : S → α) (Ok : α × Option Pub9 → Prop)
    {run : ℕ → S → Except String (List Claim × S)} (h : Idle run) : Still φ Ok run fsNone :=
  ⟨fun n e _ _ hr => (congrArg Prod.snd (Except.ok.inj ((h n e).symm.trans hr))).symm,
    fun _ n e _ _ _ hr =>
      ⟨[], rfl, (congrArg Prod.fst (Except.ok.inj ((h n e).symm.trans hr))).symm⟩⟩

/-- **RunOk OF AN IDLE RUN: NO PREMISE.** -/
theorem idle_runOk [Field K] (ρ : Reading K) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (Fu : S → Prop) {run : ℕ → S → Except String (List Claim × S)} (h : Idle run)
    (ent : α × Option Pub9 → Bound K → ℕ → ℕ → ℕ → K) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) run (plainTm (valsStill ρ fsNone ent)) (lenStill fsNone) :=
  still_runOk ρ φ Ok Fu run fsNone (idle_still φ Ok h)
    (fun _ l _ _ hl _ f hf => by
      obtain rfl : [] = l := Option.some.inj hl
      exact nomatch hf) ent
    (fun _ l _ _ _ _ _ _ hl f hf => by
      obtain rfl : [] = l := Option.some.inj hl
      exact nomatch hf)

/-- It keeps the door. -/
theorem idle_door {run : ℕ → S → Except String (List Claim × S)} (h : Idle run) (n : ℕ) (e : S)
    (c : List Claim) (e₁ : S) (hr : run n e = .ok (c, e₁)) : KeepsDoor atS e e₁ := by
  obtain rfl : e = e₁ := congrArg Prod.snd (Except.ok.inj ((h n e).symm.trans hr))
  exact fun a ha => ⟨a, ha, rfl, rfl⟩

end VerifiableInference.Desc.StillRun

#print axioms VerifiableInference.Desc.StillRun.idle_still
#print axioms VerifiableInference.Desc.StillRun.idle_runOk
#print axioms VerifiableInference.Desc.StillRun.idle_door
