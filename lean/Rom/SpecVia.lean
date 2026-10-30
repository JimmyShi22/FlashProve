-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecVia.lean: a family of random oracles does not change if its points are permuted. Definitions
(`QMap`, `OComp.via`, `Adv.via`, `Table.via`, `World.pre`) and four statements (`Spec.viaWorld`,
`Spec.viaPre`, `Spec.viaBounds`, `Spec.viaConsistent`); the proofs are in Rom/Via.lean.

A point of a family S is a pair (oracle, query to it). All points are answered independently, each
uniformly in the range of its oracle. So if φ is a bijection of the points, with for each point a
bijection between the range at its image and its own range, the family "answer the point p by the
answer at φ p" has the distribution of the family itself. This file states what follows for
algorithms, adversaries and challengers (`World`, Rom/World.lean).

What it is for. A scheme whose honest algorithms query one oracle at several points that contain the
same secret string. The lemma on deferred programming (Rom/Defer.lean) requires that a secret string
be charged at most once at each oracle. One writes the honest programs with further oracles for the
later points (oracles that no one else uses), proves privacy for these programs, and comes back by
the bijection that exchanges each such point with the point of the true oracle.

Limits:
* Budgets for single oracles are not kept. `A.via ψ` queries the oracle of ψ p where A queried
  that of p. If A makes at most t queries to an oracle o, then `A.via ψ` may make t queries to each
  oracle in which ψ puts a point of o. Only the total is kept (`Adv.TotalBound`). Whoever then uses
  a bound with one term for each oracle (`Spec.defer`) must take the adversary's whole budget
  in each term: with T further oracles this costs a factor of up to T + 1 in the part of the bound
  that is linear in t.
* Nothing on an experiment in which only some of the parties are translated, but for `Spec.viaPre`,
  which only rewrites one such experiment as another. In `Spec.viaWorld` all algorithms of the
  challenger are translated and the adversary is translated back.
* Traces and views: an adversary's output is kept as it is; if it outputs its own trace, that is the
  trace of A, with the points as A named them (`A.via ψ` passes the translated answers to A's
  continuations).
-/
import Rom.World
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom

/-- A translation of queries: for the point (o, q) the point (o', q') that is queried in its place,
and how an answer of o' is read as an answer of o. (The map comes with its point, so that no cast
between ranges is ever written.) -/
abbrev QMap (S : OSpec) : Type := (o : S.ι) → S.Dom o → Σ o' : S.ι, S.Dom o' × (S.Rng o' → S.Rng o)

variable {S : OSpec} {Out In α : Type}

/-- ψ undoes φ: it sends the image of (o, q) back to (o, q), and the two maps between the ranges are
inverse to each other. -/
def QMap.Inv (φ ψ : QMap S) : Prop :=
  ∀ (o : S.ι) (q : S.Dom o), ∃ b : S.Rng o → S.Rng (φ o q).1,
    ψ (φ o q).1 (φ o q).2.1 = ⟨o, q, b⟩ ∧
    (∀ r, (φ o q).2.2 (b r) = r) ∧
    (∀ r, b ((φ o q).2.2 r) = r)

/-- φ is a bijection of the points that respects the ranges, and ψ is its inverse. -/
structure QMap.Perm (φ ψ : QMap S) : Prop where
  left : QMap.Inv φ ψ
  right : QMap.Inv ψ φ

/-- the algorithm that queries φ p where c queries p -/
def OComp.via (φ : QMap S) : OComp S α → OComp S α
  | .pure a => .pure a
  | .query o q k => .query (φ o q).1 (φ o q).2.1 fun r => (k ((φ o q).2.2 r)).via φ
  | .sample n k => .sample n fun r => (k r).via φ

/-- the adversary that queries φ p where A queries p; its calls are unchanged -/
def Adv.via (φ : QMap S) : Adv S Out In α → Adv S Out In α
  | .halt a => .halt a
  | .sample n k => .sample n fun r => (k r).via φ
  | .query o q k => .query (φ o q).1 (φ o q).2.1 fun r => (k ((φ o q).2.2 r)).via φ
  | .call m k => .call m fun a => (k a).via φ

/-- the table of lazy sampling that holds at p the translated entry at φ p -/
def Table.via (φ : QMap S) (T : Table S) : Table S := fun o q =>
  (T (φ o q).1 (φ o q).2.1).map (φ o q).2.2

/-- the challenger that answers the query p by its translated answer at φ p; its replies to calls
are unchanged -/
def World.pre (φ : QMap S) (W : World S Out In) : World S Out In where
  σ := W.σ
  answer := fun s o q => (W.answer s (φ o q).1 (φ o q).2.1).map fun x => ((φ o q).2.2 x.1, x.2)
  reply := W.reply

theorem Table.via_empty (φ : QMap S) : Table.via φ (Table.empty S) = Table.empty S := rfl


/-- A challenger whose replies are oracle algorithms over one lazily sampled table, all translated
by a bijection φ with inverse ψ: A sees what `A.via ψ` sees against the challenger with the
algorithms as they were. (Start states: `(s, T)` and `(s, Table.via φ T)`.) -/
def Spec.viaWorld : Prop :=
  ∀ (S : OSpec) (Out In τ α : Type) (φ ψ : QMap S), QMap.Perm φ ψ →
    ∀ (step : τ → Out → OComp S (In × τ)) (A : Adv S Out In α) (s : τ) (T : Table S),
      (interact (World.ofOComp fun s m => (step s m).via φ) A (s, T)).map Prod.fst
        = (interact (World.ofOComp step) (A.via ψ) (s, Table.via φ T)).map Prod.fst

/-- Any challenger after a translation: A against `W.pre ψ` is `A.via ψ` against W: the same
distribution of (output, state). For every translation and every challenger. -/
def Spec.viaPre : Prop :=
  ∀ (S : OSpec) (Out In α : Type) (ψ : QMap S) (W : World S Out In) (A : Adv S Out In α) (s : W.σ),
    interact (W.pre ψ) A s = interact W (A.via ψ) s

/-- What is kept of an adversary: every bound on A's queries in all and on its calls holds of
`A.via ψ`, and `A.via ψ` makes only calls that A makes. -/
def Spec.viaBounds : Prop :=
  ∀ (S : OSpec) (Out In α : Type) (ψ : QMap S) (A : Adv S Out In α),
    (∀ t N, A.TotalBound t N → (A.via ψ).TotalBound t N) ∧
    (∀ ok : Out → Prop, A.CallsOK ok → (A.via ψ).CallsOK ok)

/-- Consistency is kept: if W never answers a repeated query differently, neither does `W.pre ψ`,
for a bijection. -/
def Spec.viaConsistent : Prop :=
  ∀ (S : OSpec) (Out In : Type) (φ ψ : QMap S),
    QMap.Perm φ ψ → ∀ W : World S Out In, W.Consistent → (W.pre ψ).Consistent

end Rom
