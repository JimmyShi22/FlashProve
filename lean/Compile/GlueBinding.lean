-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/GlueBinding.lean: general lemmas on oracle algorithms (`OComp`, Rom/OComp.lean) and on
probabilities (`pr`, Prob/Basic.lean). No scheme occurs in this file.
  `withTrace_bind`           the trace of a sequence is the concatenation of the traces
  `runEager_withTrace_fst`   forgetting the trace gives the algorithm's output distribution back
  `DetBound c t`             c is coin-free and makes at most t queries, on every path; its rules:
                             `DetBound.mono`, `DetBound.bind`, `detBound_pure`, `detBound_ask`,
                             `DetBound.queryBound`
  `runsIn_of_mem_support`    whatever a coin-free algorithm outputs, it runs to that output within
                             its own trace (`RunsIn`, Compile/Spec.lean)
  `pr_bind_le_bind`          for two sequences with the same first part p: Pr[E] ≤ Pr[E'] if this
                             holds of the two second parts at every result of p
  `pr_pure_le_pure`          for the point masses at b and at c: Pr[E] ≤ Pr[E'] if b ∈ E implies
                             c ∈ E'
-/
import Compile.Spec
import Compile.MerkleRom
import Rom.Prefix
import Rom.Bridge

noncomputable section

namespace Compile
open Iop Rom Prob
open scoped ENNReal

/-! ## Lemmas on oracle algorithms -/

section Tools
variable {S : OSpec} {α β γ : Type}

theorem bind_pure_eta (c : OComp S (α × β)) : (c.bind fun b => OComp.pure (b.1, b.2)) = c := by
  induction c with
  | pure a => rfl
  | query o q k ih => simp only [OComp.bind, ih]
  | sample n k ih => simp only [OComp.bind, ih]

/-- The trace of a sequence is the concatenation of the traces. -/
theorem withTrace_bind (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).withTrace =
      c.withTrace.bind fun a => (g a.1).withTrace.bind fun b => OComp.pure (b.1, a.2 ++ b.2) := by
  induction c with
  | pure a => simp only [OComp.bind, OComp.withTrace, List.nil_append, bind_pure_eta]
  | query o q k ih =>
    simp only [OComp.bind, OComp.withTrace, ih, OComp.bind_assoc, List.cons_append]
  | sample n k ih => simp only [OComp.bind, OComp.withTrace, ih]

/-- Forgetting the trace gives the algorithm's output distribution back, for every family f of
oracle functions. -/
theorem runEager_withTrace_fst (f : Fam S) (c : OComp S α) :
    (c.withTrace.runEager f).map Prod.fst = c.runEager f := by
  induction c with
  | pure a => simp [OComp.withTrace, OComp.runEager, PMF.pure_map]
  | query o q k ih =>
    simp only [OComp.withTrace, OComp.runEager, OComp.runEager_bind, PMF.map_bind, PMF.pure_map]
    rw [← ih (f o q)]
    rfl
  | sample n k ih => simp only [OComp.withTrace, OComp.runEager, PMF.map_bind, ih]

/-- A coin-free algorithm that makes at most t queries, on every path. -/
def DetBound : OComp S α → ℕ → Prop
  | .pure _, _ => True
  | .query _ _ _, 0 => False
  | .query _ _ k, t + 1 => ∀ r, DetBound (k r) t
  | .sample _ _, _ => False

theorem DetBound.mono {c : OComp S α} {s t : ℕ} (h : DetBound c s) (hst : s ≤ t) :
    DetBound c t := by
  induction c generalizing s t with
  | pure a => trivial
  | query o q k ih =>
    cases s with
    | zero => exact h.elim
    | succ s =>
      cases t with
      | zero => omega
      | succ t => exact fun r => ih r (h r) (by omega)
  | sample n k _ => exact h.elim

theorem DetBound.bind {c : OComp S α} {g : α → OComp S β} {s t : ℕ} (h : DetBound c s)
    (hg : ∀ a, DetBound (g a) t) : DetBound (c.bind g) (s + t) := by
  induction c generalizing s with
  | pure a => exact (hg a).mono (by omega)
  | query o q k ih =>
    cases s with
    | zero => exact h.elim
    | succ s =>
      have : s + 1 + t = (s + t) + 1 := by omega
      rw [this]
      exact fun r => ih r (h r)
  | sample n k _ => exact h.elim

theorem detBound_pure (a : α) (t : ℕ) : DetBound (OComp.pure a : OComp S α) t := trivial

theorem detBound_ask (o : S.ι) (q : S.Dom o) : DetBound (OComp.ask o q) 1 := fun _ => trivial

theorem DetBound.queryBound {c : OComp S α} {t : ℕ} (h : DetBound c t) : c.QueryBound t := by
  induction c generalizing t with
  | pure a => trivial
  | query o q k ih =>
    cases t with
    | zero => exact h.elim
    | succ t => exact fun r => ih r (h r)
  | sample n k _ => exact h.elim

/-- Whatever a coin-free algorithm outputs, it runs to that output within its own trace. -/
theorem runsIn_of_mem_support {c : OComp S α} {t : ℕ} (h : DetBound c t) (f : Fam S) :
    ∀ o ∈ (c.withTrace.runEager f).support, RunsIn o.2 c o.1 := by
  induction c generalizing t with
  | pure a =>
    intro o ho
    simp only [OComp.withTrace, OComp.runEager, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    exact RunsIn.pure a
  | query o q k ih =>
    intro out hout
    cases t with
    | zero => exact h.elim
    | succ t =>
      simp only [OComp.withTrace, OComp.runEager, OComp.runEager_bind, PMF.mem_support_bind_iff,
        PMF.support_pure, Set.mem_singleton_iff] at hout
      obtain ⟨z, hz, rfl⟩ := hout
      exact RunsIn.query o q k (f o q) z.1 (List.mem_cons_self)
        ((ih (f o q) (h (f o q)) z hz).mono (List.subset_cons_self _ _))
  | sample n k _ => exact h.elim

end Tools

/-! ## Two comparisons of probabilities -/

section Main
variable {I X : Type} {lam : ℕ}

theorem pr_bind_le_bind {α β γ : Type} (p : PMF α) (g : α → PMF β) (g' : α → PMF γ) (E : Set β)
    (E' : Set γ) (h : ∀ a ∈ p.support, pr (g a) E ≤ pr (g' a) E') :
    pr (p.bind g) E ≤ pr (p.bind g') E' := by
  rw [pr_bind, pr_bind]
  exact expect_mono_support p h

theorem pr_pure_le_pure {β γ : Type} {b : β} {c : γ} {E : Set β} {E' : Set γ} (h : b ∈ E → c ∈ E') :
    pr (PMF.pure b) E ≤ pr (PMF.pure c) E' := by
  classical
  rw [pr_pure, pr_pure]
  by_cases hb : b ∈ E
  · rw [if_pos hb, if_pos (h hb)]
  · rw [if_neg hb]; exact zero_le _

end Main

end Compile
