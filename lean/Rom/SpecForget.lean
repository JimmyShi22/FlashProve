-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecForget.lean: an exact fact on lazily sampled oracles, as statements (`Spec.forget`,
`Spec.forgetCall`). The proofs are in Rom/Forget.lean.

An entry of the lazily sampled table that was sampled and never used is as good as no entry. A
challenger (`World`) whose replies are oracle algorithms over one shared, lazily sampled table
depends on these algorithms only through their output distribution for each fixed family of oracles.
-/
import Rom.World

namespace Rom
variable {S : OSpec} {Out In α : Type}



/-- Forget. Let two challengers reply by oracle algorithms over a shared, lazily sampled table, with
private states in τ₁ and τ₂, and let φ map τ₁ to τ₂. Suppose that for every fixed family f of
oracles each reply of the first challenger, with its new private state mapped by φ, has the
distribution of the reply of the second. Then every adversary has the same joint distribution of
output and (mapped) final private state against both, from every table. The tables of the two
experiments may differ: a query whose answer influences neither the reply nor the private state does
not change the distribution for a fixed f, so it may be made in one experiment and not in the other,
at points that are chosen adaptively, and the whole later interaction does not notice. -/
def Spec.forget : Prop :=
  ∀ (S : OSpec) (Out In α τ₁ τ₂ : Type) (step₁ : τ₁ → Out → OComp S (In × τ₁))
      (step₂ : τ₂ → Out → OComp S (In × τ₂)) (φ : τ₁ → τ₂),
    (∀ t m f, ((step₁ t m).runEager f).map (Prod.map id φ) = (step₂ (φ t) m).runEager f) →
    ∀ (A : Adv S Out In α) (t : τ₁) (T : Table S),
      (interact (World.ofOComp step₁) A (t, T)).map (fun x => (x.1, φ x.2.1)) =
        (interact (World.ofOComp step₂) A (φ t, T)).map (fun x => (x.1, x.2.1))

/-- A call that shows nothing. A call that runs an oracle algorithm, discards its result, replies
with a constant and keeps the private state can be replaced by the constant, in this sense: from
every state s and table T, the output of every adversary A has the same distribution against
`World.ofOComp step` and against `World.ofOComp step'`. -/
def Spec.forgetCall : Prop :=
  ∀ (S : OSpec) (Out In τ α : Type) (step step' : τ → Out → OComp S (In × τ)),
    (∀ s m,
      step' s m = step s m ∨
      ∃ (β : Type) (c : OComp S β) (a : In),
        step s m = c.bind (fun _ => .pure (a, s)) ∧ step' s m = .pure (a, s)) →
    ∀ (A : Adv S Out In α) (s : τ) (T : Table S),
      (interact (World.ofOComp step) A (s, T)).map Prod.fst =
        (interact (World.ofOComp step') A (s, T)).map Prod.fst

end Rom
