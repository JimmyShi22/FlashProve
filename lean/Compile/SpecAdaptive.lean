-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SpecAdaptive.lean: completeness against an adaptive environment (words of this library:
lean/GLOSSARY.md): the property, with the definitions that it needs. Compile/CompleteAdaptive.lean
has a sanity lemma: the property implies completeness (`ZKCP.Gen.HasCompletenessError`) for
batches of at most one pair, with the error at no queries and one session.
Compile/AdaptiveExit.lean carries the property to one hash function and to ZKCP/Adaptive.lean.

Sources. `sessions_of_refined` (ZKCP/Basic.lean): for every i and adaptively chosen pairs
(x_j, w_j), j ≤ N, with (i, x_j, w_j) ∈ R, and π_j ← P^f(isk, x_j, w_j): Pr[ V rejects π_j for some
j ≤ N ] ≤
α_C + N α_P. It is derived there from refined completeness (`HasRefinedCompletenessError`),
which is out of reach for a scheme whose failures depend on a hash of the instance together with a
salt, over a large set of instances: a chooser that knows the whole oracle finds a bad instance
(argued, not proved here).
This file states the conclusion directly, for an
environment that sees all that is released and makes at most t oracle queries:

  HasAdaptiveCompleteness   the property, for any argument system over any family of oracles
                            (batches of one).

Limits: this library proves the property of no scheme: each theorem that names it has it as a
hypothesis (`completeness_of_adaptive`, Compile/CompleteAdaptive.lean; `adaptive_overOne`,
`adaptive_of_gen`, Compile/AdaptiveExit.lean).
-/
import Compile.Spec

set_option autoImplicit false

noncomputable section

namespace Compile

open Iop Rom Prob ZKCP
open scoped ENNReal

/-! ## The property, for any argument system -/

namespace Adaptive

/-- The environment. It halts, queries an oracle, flips coins, or names the next pair (x, w); it
then receives the honest proof and V's bit on it. So each choice may depend on ivk, on all earlier
proofs and bits, on its queries and on its coins. It is given neither isk nor the oracles as a
whole. -/
inductive CEnv (S : OSpec) (X Wn Pf : Type) : Type
  | halt : CEnv S X Wn Pf
  | query (o : S.ι) (q : S.Dom o) (k : S.Rng o → CEnv S X Wn Pf) : CEnv S X Wn Pf
  | sample (n : ℕ) (k : Fin (n + 1) → CEnv S X Wn Pf) : CEnv S X Wn Pf
  | session (x : X) (w : Wn) (k : Pf → Bool → CEnv S X Wn Pf) : CEnv S X Wn Pf

variable {S : OSpec} {I X Wn PP IVK ISK Pf : Type}

/-- at most t queries, on every path -/
def CEnv.QueryBound : CEnv S X Wn Pf → ℕ → Prop
  | .halt, _ => True
  | .query _ _ _, 0 => False
  | .query _ _ k, t + 1 => ∀ r, (k r).QueryBound t
  | .sample _ k, t => ∀ r, (k r).QueryBound t
  | .session _ _ k, t => ∀ π b, (k π b).QueryBound t

/-- every pair that the environment names is allowed, whatever it has received -/
def CEnv.Valid (ok : X → Wn → Prop) : CEnv S X Wn Pf → Prop
  | .halt => True
  | .query _ _ k => ∀ r, (k r).Valid ok
  | .sample _ k => ∀ r, (k r).Valid ok
  | .session x w k => ok x w ∧ ∀ π b, (k π b).Valid ok

/-- the one entry of a list with one slot -/
def one {β : Type} {a : β} (s : Gen.Slots Pf [a]) : Pf :=
  s.val[0]'(by rw [s.property]; exact Nat.zero_lt_one)

variable (A : Gen.Arg S I X Wn IVK ISK Pf)

/-- The sessions on one key; n is the number of sessions still allowed. The result is true if V has
accepted every proof. -/
def loop (ivk : IVK) (isk : ISK) : CEnv S X Wn Pf → ℕ → OComp S Bool
  | .halt, _ => pure true
  | .query o q k, n => .query o q fun r => loop ivk isk (k r) n
  | .sample m k, n => .sample m fun r => loop ivk isk (k r) n
  | .session _ _ _, 0 => pure true
  | .session x w k, n + 1 =>
      (A.P isk [(x, w)]).bind fun πs => (A.V ivk x (one πs)).bind fun b =>
        (loop ivk isk (k (one πs) b) n).bind fun rest => pure (b && rest)

/-- The experiment: an honest key for i, then at most N honest sessions on pairs that the
environment chooses. -/
def exp (E : IVK → CEnv S X Wn Pf) (i : I) (N : ℕ) : OComp S Bool :=
  (A.C i).bind fun key => loop A key.1 key.2 (E key.1) N

/-- Completeness against an adaptive environment (the event of the claim of `sessions_of_refined`
(ZKCP/Basic.lean), with a bound α t N, for an environment with t queries):
for each index i, all t and N, and each environment E (it may depend on i, and is handed ivk) that
makes at most t queries and chooses only pairs in R.yes i: the probability that V rejects at least
one of the first N honest proofs is at most α t N. -/
def HasAdaptiveCompleteness (R : Gen.RelPair I X Wn PP) (α : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (i : I) (t N : ℕ) (E : IVK → CEnv S X Wn Pf), (∀ ivk, (E ivk).QueryBound t) →
    (∀ ivk, (E ivk).Valid (R.yes i)) → Rom.Pr (exp A E i N) (fun _ => {b | b = false}) ≤ α t N

end Adaptive

end Compile
