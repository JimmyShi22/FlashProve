-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_life2_Erase.lean: mode R of a token program is the lazy run of its erasure (words of
this library: lean/GLOSSARY.md; modes: Rom/Defer.lean).

`Compile.erase` (Compile/Star.lean) forgets the rules for tokens: a token is an index into a list of
strings. This file shows, for any token program:

  `run_false_eq_erase`   The run in mode R, of which only the result, the strings and the table are
                         kept, is the lazy run of `erase`.
  `erase_virt`           The lazy run of `erase` of the program under the renumbering of tokens
                         (Compile/Step1_life2_Virt.lean), its list of strings mapped by `viewVals`,
                         is the lazy run of `erase` of the program on the list without the δ
                         strings, if the list has at least N₀ + δ strings.
  `run_false_virt`       Both together.
-/
import Compile.Star
import Compile.Step1_life2_Virt
import Prob.Count

noncomputable section

namespace Compile
namespace Life2
open Rom Prob

/-! ## Bits -/

/-- the numbers below 2^ℓ and the strings of ℓ bits -/
def bitsE (ℓ : ℕ) : Fin (2 ^ ℓ - 1 + 1) ≃ (Fin ℓ → Bool) where
  toFun r := fun i => r.val.testBit i
  invFun u := ⟨Nat.ofBits u, by
    have h1 := Nat.ofBits_lt_two_pow u
    have h2 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
    omega⟩
  left_inv r := by
    apply Fin.ext
    have h2 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
    show Nat.ofBits (fun i : Fin ℓ => r.val.testBit i) = r.val
    rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt (by have := r.2; omega)]
  right_inv u := by
    funext i
    show (Nat.ofBits u).testBit i = u i
    rw [Nat.testBit_ofBits_lt _ _ i.2]

theorem unif_bits_bind {γ : Type} (ℓ : ℕ) (F : (Fin ℓ → Bool) → PMF γ) :
    ((PMF.uniformOfFintype (Fin (2 ^ ℓ - 1 + 1))).bind fun r => F fun i => r.val.testBit i)
      = (PMF.uniformOfFintype (Fin ℓ → Bool)).bind F := by
  have h : (PMF.uniformOfFintype (Fin (2 ^ ℓ - 1 + 1))).map (bitsE ℓ) =
      PMF.uniformOfFintype (Fin ℓ → Bool) :=
    map_unif_equiv (bitsE ℓ)
  rw [← h, PMF.bind_map]
  rfl

variable {S : OSpec} {sp : Split S} {α : Type}

theorem runLazy_query (o : S.ι) (q : S.Dom o) (k : S.Rng o → OComp S α) (T : Table S) :
    (OComp.query o q k).runLazy T = (lazyAnswer T o q).bind fun p => (k p.1).runLazy p.2 := by
  cases h : T o q with
  | none => simp only [OComp.runLazy, lazyAnswer, h, PMF.bind_map, Function.comp_def]
  | some r => simp only [OComp.runLazy, lazyAnswer, h, PMF.pure_bind]

theorem releaseAll_false (shown : List ℕ) (evs : List (Ev S)) (T : Table S) :
    (releaseAll false shown evs T).2 = T := by
  induction evs with
  | nil => rfl
  | cons e es ih =>
    by_cases h : (!e.released && shown.contains e.charged) = true
    · rw [releaseAll_cons_pos h]
      exact ih
    · rw [releaseAll_cons_neg h]
      exact ih

/-- Mode R, of which only the result, the strings and the table are kept, is the lazy run of
`erase`. -/
theorem run_false_eq_erase (c : Step S sp α) :
    ∀ D : DSt S, (c.run false D).map (fun x => ((x.1, x.2.vals), x.2.table)) =
      (erase c D.vals).runLazy D.table := by
  induction c with
  | pure a =>
    intro D
    simp only [Step.run, erase, OComp.runLazy, PMF.pure_map]
  | sample n k ih =>
    intro D
    simp only [Step.run, erase, OComp.runLazy, PMF.map_bind, ih]
  | plain o q k ih =>
    intro D
    simp only [Step.run, erase, runLazy_query, PMF.map_bind, ih]
  | fresh ℓ k ih =>
    intro D
    simp only [Step.run, erase, OComp.runLazy, PMF.map_bind, ih]
    exact (unif_bits_bind ℓ fun u =>
      (erase (k D.vals.length) (D.vals ++ [List.ofFn u])).runLazy D.table).symm
  | marked o t us pt inj k ih =>
    intro D
    simp only [Step.run, erase, runLazy_query, PMF.map_bind, ih, Bool.false_eq_true, if_false]
    rfl
  | reveal ts k ih =>
    intro D
    simp only [Step.run, erase, ih, releaseAll_false]
    rfl

/-- If N₀ + δ ≤ vs.length, the lazy run of `erase` of the renumbered program on vs, its list of
strings mapped by `viewVals`, is the lazy run of `erase c` on `viewVals N₀ δ vs`. -/
theorem erase_virt {N₀ δ : ℕ} (c : Step S sp α) :
    ∀ (vs : List Bits), N₀ + δ ≤ vs.length → ∀ T : Table S,
      ((erase (virt N₀ δ c) vs).runLazy T).map (fun x => ((x.1.1, viewVals N₀ δ x.1.2), x.2))
        = (erase c (viewVals N₀ δ vs)).runLazy T := by
  induction c with
  | pure a =>
    intro vs _ T
    simp only [virt, erase, OComp.runLazy, PMF.pure_map]
  | sample n k ih =>
    intro vs h T
    simp only [virt, erase, OComp.runLazy, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r vs h T)
  | plain o q k ih =>
    intro vs h T
    simp only [virt, erase, runLazy_query, PMF.map_bind]
    exact congrArg _ (funext fun p => ih p.1 vs h p.2)
  | fresh ℓ k ih =>
    intro vs h T
    have hl : (viewVals N₀ δ vs).length = vs.length - δ := by have := length_viewVals h; omega
    simp only [virt, erase, OComp.runLazy, PMF.map_bind, hl]
    refine congrArg _ (funext fun r => ?_)
    rw [ih _ _ (by simp only [List.length_append]; omega), viewVals_append h]
  | marked o t us pt inj k ih =>
    intro vs h T
    have hl : (viewVals N₀ δ vs).length = vs.length - δ := by have := length_viewVals h; omega
    have hus : ((us.map (up N₀ δ)).map fun u => vs.getD u []) =
        us.map fun u => (viewVals N₀ δ vs).getD u [] := by
      rw [List.map_map]
      exact List.map_congr_left fun v _ => (getD_viewVals h v).symm
    simp only [virt, erase, runLazy_query, PMF.map_bind, hl, hus, getD_viewVals h]
    refine congrArg _ (funext fun p => ?_)
    rw [ih _ _ _ (by simp only [List.length_append]; omega), viewVals_append h]
  | reveal ts k ih =>
    intro vs h T
    have hts : ((ts.map (up N₀ δ)).map fun u => vs.getD u []) =
        ts.map fun u => (viewVals N₀ δ vs).getD u [] := by
      rw [List.map_map]
      exact List.map_congr_left fun v _ => (getD_viewVals h v).symm
    simp only [virt, erase, hts]
    exact ih _ vs h T

/-- If N₀ + δ ≤ D.vals.length, mode R of the renumbered program, of which the result, the strings
mapped by `viewVals` and the table are kept, is the lazy run of `erase c` on
`viewVals N₀ δ D.vals`. -/
theorem run_false_virt {N₀ δ : ℕ} (c : Step S sp α) (D : DSt S) (h : N₀ + δ ≤ D.vals.length) :
    ((virt N₀ δ c).run false D).map (fun x => ((x.1, viewVals N₀ δ x.2.vals), x.2.table))
      = (erase c (viewVals N₀ δ D.vals)).runLazy D.table := by
  rw [← erase_virt c D.vals h, ← run_false_eq_erase, PMF.map_comp]
  rfl

end Life2
end Compile
