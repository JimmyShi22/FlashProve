-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/CompleteUnif.lean: algorithms that query only some oracles. `Only P c`: all queries of the
algorithm c, on all paths, go to oracles with the property P. A sequence of such algorithms is one
(`Only.bind`). Under lazily sampled oracles (`OComp.runLazy`, Rom/OComp.lean) the table of an oracle
that is not queried does not change (`Only.table`; `T : Table S`, Rom/OSpec.lean: a partial table:
what lazy sampling has fixed so far). Also here: every distribution on `Unit` is the point mass
(`unif_unit_eq`).
-/
import Compile.CompleteRef

noncomputable section

namespace Compile.Cmpl
open Iop Rom Prob
open scoped ENNReal

/-! ## Algorithms that query only some oracles -/

section Only

variable {S : OSpec} {α β : Type}

/-- All queries of the algorithm, on all paths, go to oracles with the property P. -/
def Only (P : S.ι → Prop) : OComp S α → Prop
  | .pure _ => True
  | .query o _ k => P o ∧ ∀ r, Only P (k r)
  | .sample _ k => ∀ r, Only P (k r)

variable {P : S.ι → Prop}

theorem Only.bind {c : OComp S α} {g : α → OComp S β} (hc : Only P c) (hg : ∀ a, Only P (g a)) :
    Only P (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | query o q k ih => exact ⟨hc.1, fun r => ih r (hc.2 r)⟩
  | sample n k ih => exact fun r => ih r (hc r)

/-- The table of an oracle that is not queried does not change. -/
theorem Only.table {c : OComp S α} (hc : Only P c) :
    ∀ (T : Table S), ∀ x ∈ (c.runLazy T).support, ∀ o, ¬ P o → x.2 o = T o := by
  induction c with
  | pure a =>
    intro T x hx o _
    simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | query o q k ih =>
    intro T x hx o' ho'
    have hne : o' ≠ o := fun h => ho' (h ▸ hc.1)
    simp only [OComp.runLazy] at hx
    cases hT : T o q with
    | some r =>
      rw [hT] at hx
      exact ih r (hc.2 r) T x hx o' ho'
    | none =>
      rw [hT] at hx
      obtain ⟨r, -, hx'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
      rw [ih r (hc.2 r) _ x hx' o' ho', Table.set, Function.update_of_ne hne]
  | sample n k ih =>
    intro T x hx o' ho'
    simp only [OComp.runLazy] at hx
    obtain ⟨r, -, hx'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    exact ih r (hc r) T x hx' o' ho'

end Only

variable {I X : Type} {lam K : ℕ}

/-! ## Distributions on `Unit` -/

theorem unif_unit_eq (μ : PMF Unit) : μ = PMF.pure () := by
  refine PMF.ext fun u => ?_
  have h := μ.tsum_coe
  rw [tsum_fintype] at h
  simpa using h

end Compile.Cmpl
