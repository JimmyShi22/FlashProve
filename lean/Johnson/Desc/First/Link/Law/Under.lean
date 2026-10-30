-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/Under.lean: A RUN BEHIND A GUARD: `Under run r`: every yes of run is a
yes of r with the same return. The batching kind's premises on a run (`RunOk`, `QuietOk`), the
door's duty and «keeps a field» name the run in a premise alone: SO THEY PASS FROM r TO EVERY RUN
UNDER IT. Small theorems: tools for the assembly of the kinds' laws.

Why. A description may lay each kind's runs behind a guard that only adds refusals. The run that
then stands at an entry of a link's order is not the kind's own run, but a run under it. The ties of
the assembly (PayLayers.lean, PayAttention.lean, PayHead.lean) are therefore stated with `Under`,
not with an equation.

Limits. Tools. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.IdleRun
import Johnson.Desc.First.Batch.Law.MovesDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens)
open VerifiableInference.Desc.K9L

variable {T P K β : Type}

/-- Every yes of run is a yes of r, with the same return. -/
def Under (run r : ℕ → T → Except String (List Claim × T)) : Prop :=
  ∀ n e c e₁, run n e = .ok (c, e₁) → r n e = .ok (c, e₁)

/-- The like of a run behind the batching. -/
def UnderAfter (run r : T → Except String T) : Prop := ∀ e e₁, run e = .ok e₁ → r e = .ok e₁

theorem under_refl (r : ℕ → T → Except String (List Claim × T)) : Under r r := fun _ _ _ _ h => h

theorem underAfter_refl (r : T → Except String T) : UnderAfter r r := fun _ _ h => h

theorem under_of_eq {run r : ℕ → T → Except String (List Claim × T)} (h : run = r) :
    Under run r := h ▸ under_refl run

theorem underAfter_of_eq {run r : T → Except String T} (h : run = r) : UnderAfter run r :=
  h ▸ underAfter_refl run

/-- The run that returns no claim and hands the record back. -/
def idle0 : ℕ → T → Except String (List Claim × T) := fun _ s => .ok ([], s)

/-- The door's duty passes. -/
theorem door_under (X : Lens T) {run r : ℕ → T → Except String (List Claim × T)}
    (hu : Under run r) (h : ∀ n e c e₁, r n e = .ok (c, e₁) → KeepsDoor X e e₁) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → KeepsDoor X e e₁ :=
  fun n e c e₁ hr => h n e c e₁ (hu n e c e₁ hr)

theorem doorAfter_under (X : Lens T) {run r : T → Except String T} (hu : UnderAfter run r)
    (h : ∀ e e₁, r e = .ok e₁ → KeepsDoor X e e₁) : ∀ e e₁, run e = .ok e₁ → KeepsDoor X e e₁ :=
  fun e e₁ hr => h e e₁ (hu e e₁ hr)

/-- «Keeps a field» passes. -/
theorem keep_under (f : T → β) {run r : ℕ → T → Except String (List Claim × T)}
    (hu : Under run r) (h : ∀ n e c e₁, r n e = .ok (c, e₁) → f e₁ = f e) :
    ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e :=
  fun n e c e₁ hr => h n e c e₁ (hu n e c e₁ hr)

theorem keepAfter_under (f : T → β) {run r : T → Except String T} (hu : UnderAfter run r)
    (h : ∀ e e₁, r e = .ok e₁ → f e₁ = f e) : ∀ e e₁, run e = .ok e₁ → f e₁ = f e :=
  fun e e₁ hr => h e e₁ (hu e e₁ hr)

/-- QuietOk passes. -/
theorem quietOk_under (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)
    {run r : T → Except String T} (hu : UnderAfter run r) (h : QuietOk X O Fx r) :
    QuietOk X O Fx run :=
  fun q e a e₁ hf hg ha hs hr => h q e a e₁ hf hg ha hs (hu e e₁ hr)

/-- **RunOk passes.** -/
theorem runOk_under [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)
    {run r : ℕ → T → Except String (List Claim × T)} (hu : Under run r)
    {tm : ℕ → P → Bound K → List (ℕ × K)} {len : P → ℕ} (h : RunOk ρ X O Fx r tm len) :
    RunOk ρ X O Fx run tm len :=
  fun q front e a c e₁ hf hg ha hs hr => h q front e a c e₁ hf hg ha hs (hu front e c e₁ hr)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.door_under
#print axioms VerifiableInference.Desc.LinkJoin.keep_under
#print axioms VerifiableInference.Desc.LinkJoin.quietOk_under
#print axioms VerifiableInference.Desc.LinkJoin.runOk_under
