-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondCongr.lean: the condition of the law of a proximity test (the kind K12),
`K12Condition` (Johnson/Desc/K12/Law/ChainHolds.lean), reads its radii at the place's stages alone.
Statements and proofs.

Why. The radii stand in the condition as a function of a stage's numbers. Two functions that agree
at the place's stages are two terms; what is shown at one is wanted at the other.
Main names:
  `codesAt_congr`: `CodesAt` at radii that agree at the list's stages.
  `stepEndX_congr`, `stepMidX_congr`, `chainFrom_congr`: the place's chain at `Letters.at` is the
    same chain, as an equation, at radii that agree at its stages.
  `k12Condition_congr`: the condition at rad gives the condition at rad'.
Limits: nothing on which radii a plan means. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.ChainHolds

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open scoped ENNReal

variable (L mC mS mW : Sg → ℕ → ℕ) (rad rad' : Sg → ℕ)

theorem codesAt_congr : ∀ l : List Fmt.M1.Stage, (∀ a ∈ l, rad (sgOf a) = rad' (sgOf a)) →
    CodesAt L mC mS mW rad l → CodesAt L mC mS mW rad' l
  | [], _, _ => trivial
  | [a], h, hc => by
    have e := h a (List.mem_singleton.2 rfl)
    unfold CodesAt at hc ⊢
    rw [← e]
    exact hc
  | a :: b :: rest, h, hc => by
    have ea := h a List.mem_cons_self
    have eb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    unfold CodesAt at hc ⊢
    rw [← ea, ← eb]
    exact ⟨hc.1, hc.2.1, hc.2.2.1,
      codesAt_congr (b :: rest) (fun x hx => h x (List.mem_cons_of_mem _ hx)) hc.2.2.2⟩

theorem stepEndX_congr (a b : Fmt.M1.Stage) (hf : CsFit (sgOf a) (sgOf b)) (dE dT dS dC : WR)
    (next : Chain (sgOf b)) (ea : rad (sgOf a) = rad' (sgOf a))
        (eb : rad (sgOf b) = rad' (sgOf b)) :
    stepEndX (.at L mC mS mW rad) a b hf dE dT dS dC next =
      stepEndX (.at L mC mS mW rad') a b hf dE dT dS dC next := by
  unfold stepEndX
  simp only [Letters.at]
  rw [ea, eb]

theorem stepMidX_congr (a b : Fmt.M1.Stage) (hf : CsFit (sgOf a) (sgOf b)) (dE dT dS dC : WR)
    (next : Chain (sgOf b)) (ea : rad (sgOf a) = rad' (sgOf a))
        (eb : rad (sgOf b) = rad' (sgOf b)) :
    stepMidX (.at L mC mS mW rad) a b hf dE dT dS dC next =
      stepMidX (.at L mC mS mW rad') a b hf dE dT dS dC next := by
  unfold stepMidX
  simp only [Letters.at]
  rw [ea, eb]

theorem chainFrom_congr : ∀ (rest : List Fmt.M1.Stage) (a : Fmt.M1.Stage) (l : List WR),
    (∀ x ∈ a :: rest, rad (sgOf x) = rad' (sgOf x)) →
    chainFrom (.at L mC mS mW rad) rest a l = chainFrom (.at L mC mS mW rad') rest a l
  | [], a, l, h => by
    have ea := h a List.mem_cons_self
    unfold chainFrom
    split
    · simp only [Letters.at]
      rw [ea]
    · rfl
  | b :: rest, a, l, h => by
    have ea := h a List.mem_cons_self
    have eb := h b (List.mem_cons_of_mem _ List.mem_cons_self)
    have ih := fun l'' => chainFrom_congr rest b l'' (fun x hx => h x (List.mem_cons_of_mem _ hx))
    unfold chainFrom
    split
    · split
      · split
        · rw [ih]
          congr 1
          funext next
          split
          · exact stepEndX_congr L mC mS mW rad rad' a b _ _ _ _ _ next ea eb
          · exact stepMidX_congr L mC mS mW rad rad' a b _ _ _ _ _ next ea eb
        · rfl
      · rfl
    · rfl

/-- **The condition reads the radii at the place's stages alone.** -/
theorem k12Condition_congr {p : P12} {K : Codes} {εs : ℝ≥0∞}
    (h : ∀ a ∈ p.nums.stages, rad (sgOf a) = rad' (sgOf a))
    (hK : K12Condition L mC mS mW rad p K εs) : K12Condition L mC mS mW rad' p K εs :=
  ⟨hK.pub, hK.spend, codesAt_congr L mC mS mW rad rad' _ h hK.codes,
    fun a rest w0 l c hs hw hc => hK.small a rest w0 l c hs hw (by
      rw [chainFrom_congr L mC mS mW rad rad' rest a l (by rw [← hs]; exact h)]
      exact hc)⟩

end H2K.Pub

#print axioms H2K.Pub.k12Condition_congr
