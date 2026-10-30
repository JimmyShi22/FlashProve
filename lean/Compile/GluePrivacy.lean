-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/GluePrivacy.lean: three small facts. A run with lazily sampled oracles (`OComp.runLazy`,
Rom/OComp.lean), unfolded at `pure` and at a query (`runLazy_pure`, `runLazy_query`; `lazyAnswer`:
Rom/World.lean). An adversary with at most t queries and at most N calls (`Adv.TotalBound`,
Rom/World.lean) has at most t queries and at most N + 1 calls (`totalBound_succ`).
-/
import Compile.Spec
import Rom.EagerLazy

set_option autoImplicit false

noncomputable section

namespace Compile.Glue

open Iop Rom Prob ZKCP
open scoped ENNReal

/-! ## Lazy sampling, two small facts -/

theorem runLazy_pure {S : OSpec} {α : Type} (a : α) (T : Table S) :
    (pure a : OComp S α).runLazy T = PMF.pure (a, T) := rfl

theorem runLazy_query {S : OSpec} {α : Type} (o : S.ι) (q : S.Dom o)
    (k : S.Rng o → OComp S α) (T : Table S) :
    (OComp.query o q k).runLazy T = (lazyAnswer T o q).bind fun a => (k a.1).runLazy a.2 := by
  unfold lazyAnswer
  simp only [OComp.runLazy]
  cases T o q with
  | none => simp only [PMF.bind_map, Function.comp_def]
  | some r => simp only [PMF.pure_bind]

variable {I X : Type} {lam : ℕ} (p : Params)

/-! ## One more call -/

theorem totalBound_succ {S : OSpec} {Out In α : Type} (A : Adv S Out In α) :
    ∀ t N, A.TotalBound t N → A.TotalBound t (N + 1) := by
  induction A with
  | halt a => intro t N _; trivial
  | sample n k ih => intro t N h r; exact ih r t N (h r)
  | query o q k ih =>
    intro t N h
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => ih r t N (h r)
  | call m k ih =>
    intro t N h
    cases N with
    | zero => exact h.elim
    | succ N => exact fun a => ih a t N (h a)

end Compile.Glue

