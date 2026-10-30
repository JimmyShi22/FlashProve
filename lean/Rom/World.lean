-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/World.lean: interactive experiments, made of an adversary that makes oracle queries and calls
(`Adv`) and the challenger that answers it, together with the oracles (`World`).

`realExp` and `idealExp` of ZKCP/Defs.lean, in the more general form of
ZKCP/Gen.lean, are written elsewhere as values of `World`, and so are hybrids of the privacy proofs.
`Spec.upToBad` states the identical-until-bad lemma; it is proved in Rom/UpToBad.lean.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
-/
import Rom.OComp
import Prob.Tv
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom
variable {S : OSpec} {Out In α : Type}

/-- An adversary: it halts with an output, flips coins, queries an oracle, or makes a call m and
receives an answer.
Its output may be its whole view, so a bound for all adversaries bounds the distance of the
views. -/
inductive Adv (S : OSpec) (Out In α : Type) : Type
  | halt (a : α) : Adv S Out In α
  | sample (n : ℕ) (k : Fin (n + 1) → Adv S Out In α) : Adv S Out In α
  | query (o : S.ι) (q : S.Dom o) (k : S.Rng o → Adv S Out In α) : Adv S Out In α
  | call (m : Out) (k : In → Adv S Out In α) : Adv S Out In α

/-- at most t o queries to oracle o and at most N calls, on every path -/
def Adv.Bounded : Adv S Out In α → (S.ι → ℕ) → ℕ → Prop
  | .halt _, _, _ => True
  | .sample _ k, t, N => ∀ r, (k r).Bounded t N
  | .query o _ k, t, N => 0 < t o ∧ ∀ r, (k r).Bounded (Function.update t o (t o - 1)) N
  | .call _ _, _, 0 => False
  | .call _ k, t, N + 1 => ∀ a, (k a).Bounded t N

/-- at most t queries in all and at most N calls, on every path -/
def Adv.TotalBound : Adv S Out In α → ℕ → ℕ → Prop
  | .halt _, _, _ => True
  | .sample _ k, t, N => ∀ r, (k r).TotalBound t N
  | .query _ _ _, 0, _ => False
  | .query _ _ k, t + 1, N => ∀ r, (k r).TotalBound t N
  | .call _ _, _, 0 => False
  | .call _ k, t, N + 1 => ∀ a, (k a).TotalBound t N

/-- every call that the adversary makes is allowed -/
def Adv.CallsOK (ok : Out → Prop) : Adv S Out In α → Prop
  | .halt _ => True
  | .sample _ k => ∀ r, (k r).CallsOK ok
  | .query _ _ k => ∀ r, (k r).CallsOK ok
  | .call m k => ok m ∧ ∀ a, (k a).CallsOK ok

/-- The challenger of an experiment, together with the oracles: a state, a randomized answer to each
oracle query, a randomized reply to each call. -/
structure World (S : OSpec) (Out In : Type) where
  σ : Type
  answer : σ → (o : S.ι) → S.Dom o → PMF (S.Rng o × σ)
  reply : σ → Out → PMF (In × σ)

/-- The challenger never answers a repeated query differently (`Trace.Consistent`: the
answers must be consistent): it keeps a table of the answers that it has given, answers from it, and
no move ever changes an entry of it. -/
def World.Consistent (W : World S Out In) : Prop :=
  ∃ seen : W.σ → Table S,
    (∀ s o q r, seen s o q = some r → ∀ x ∈ (W.answer s o q).support, x.1 = r) ∧
    (∀ s o q, ∀ x ∈ (W.answer s o q).support, seen x.2 o q = some x.1 ∧
      ∀ o' q' r', seen s o' q' = some r' → seen x.2 o' q' = some r') ∧
    (∀ s m, ∀ x ∈ (W.reply s m).support, ∀ o q r, seen s o q = some r → seen x.2 o q = some r)

/-- the run of an adversary against a challenger, from a state -/
def interact (W : World S Out In) : Adv S Out In α → W.σ → PMF (α × W.σ)
  | .halt a, s => PMF.pure (a, s)
  | .sample n k, s => (PMF.uniformOfFintype (Fin (n + 1))).bind fun r => interact W (k r) s
  | .query o q k, s => (W.answer s o q).bind fun p => interact W (k p.1) p.2
  | .call m k, s => (W.reply s m).bind fun p => interact W (k p.1) p.2

/-- lazy answer from a table -/
def lazyAnswer (T : Table S) (o : S.ι) (q : S.Dom o) : PMF (S.Rng o × Table S) :=
  match T o q with
  | some r => PMF.pure (r, T)
  | none => (PMF.uniformOfFintype (S.Rng o)).map fun r => (r, T.set o q r)

/-- A challenger whose replies are oracle algorithms over one shared, lazily sampled table, with a
private state τ. -/
def World.ofOComp {τ : Type} (step : τ → Out → OComp S (In × τ)) :
    World S Out In where
  σ := τ × Table S
  answer := fun s o q => (lazyAnswer s.2 o q).map fun p => (p.1, (s.1, p.2))
  reply := fun s m => ((step s.1 m).runLazy s.2).map fun p => (p.1.1, (p.1.2, p.2))

/-- Identical until bad, for interactive experiments. Rel couples the states; while bad has not
occurred in W₂, each move of W₁ and W₂ from related states can be coupled so that answers agree and
states stay related, or bad occurs. -/
def StepCoupled (W₁ W₂ : World S Out In) (Rel : W₁.σ → W₂.σ → Prop) (bad : W₂.σ → Prop) : Prop :=
  (∀ s₁ s₂ o q, Rel s₁ s₂ → ¬ bad s₂ → ∃ c : PMF ((S.Rng o × W₁.σ) × (S.Rng o × W₂.σ)),
      c.map Prod.fst = W₁.answer s₁ o q ∧ c.map Prod.snd = W₂.answer s₂ o q ∧
      ∀ x ∈ c.support, bad x.2.2 ∨ (x.1.1 = x.2.1 ∧ Rel x.1.2 x.2.2)) ∧
  (∀ s₁ s₂ m, Rel s₁ s₂ → ¬ bad s₂ → ∃ c : PMF ((In × W₁.σ) × (In × W₂.σ)),
      c.map Prod.fst = W₁.reply s₁ m ∧ c.map Prod.snd = W₂.reply s₂ m ∧
      ∀ x ∈ c.support, bad x.2.2 ∨ (x.1.1 = x.2.1 ∧ Rel x.1.2 x.2.2)) ∧
  -- once bad holds, it holds after every further move
  (∀ s₂ o q, bad s₂ → ∀ x ∈ (W₂.answer s₂ o q).support, bad x.2) ∧
  (∀ s₂ m, bad s₂ → ∀ x ∈ (W₂.reply s₂ m).support, bad x.2)

def Spec.upToBad : Prop :=
  ∀ (S : OSpec) (Out In α : Type) (W₁ W₂ : World S Out In)
      (Rel : W₁.σ → W₂.σ → Prop) (bad : W₂.σ → Prop),
    StepCoupled W₁ W₂ Rel bad →
    ∀ (A : Adv S Out In α) s₁ s₂, Rel s₁ s₂ →
      tv ((interact W₁ A s₁).map Prod.fst) ((interact W₂ A s₂).map Prod.fst) ≤
        pr (interact W₂ A s₂) {x | bad x.2}

end Rom
