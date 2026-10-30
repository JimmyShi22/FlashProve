-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/Window.lean: random combinations with coefficients in {-1, 0, 1}.

The range proof multiplies a hidden integer matrix Y by a random matrix Ξ whose entries are
independent, 0 with probability 1/2 and ±1 with probability 1/4 each, and asks that all entries of
the product are in a window [-t, t). This file has the two facts about such combinations, without
any protocol, field or matrix layout.

  1. Soundness. Fix one coordinate. If a test can never pass both with the coefficient 0 and with a
     coefficient ±1 at that coordinate, the other coefficients being the same, then it passes for at
     most half of the coefficient vectors, and r independent tests all pass for at most the fraction
     2^(-r).
  2. Completeness and privacy (the window event). For integers a with Σ a² ≤ V (V > 0, t ≥ 0), Σ ξ a
     leaves the window [-t, t) with probability at most 2 exp(-t²/V); a union over the entries gives
     the bound on ε_win, the probability of the window event `Win` (`pr_win_le`).

A coefficient is given by two uniform bits, so that the challenge space is a finite type with the
uniform distribution and the basic bounds are counts (`Prob.cnt`); the forms with `Prob.pr` are
derived from the counts.

Notation: a cell: an entry of a matrix Y_μ; β: t = 2^(β-1); n_Ψ: the number of entries of all the
matrices Y_μ Ξ_μ (docstring of `pr_win_le`).
Terms: lean/GLOSSARY.md.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Prob.Count

open scoped ENNReal
open Finset

namespace Prob

/-! ## 1. Coefficients -/

/-- One coefficient, as two bits: the support bit and the sign bit. -/
abbrev Coef : Type := Bool × Bool

/-- The value of a coefficient: 0 if the support bit is 0; otherwise +1 or -1 by the sign bit. -/
def Coef.val : Coef → ℤ
  | (false, _) => 0
  | (true, false) => 1
  | (true, true) => -1

/-- The coefficient with the support bit inverted. -/
def Coef.flip (a : Coef) : Coef := (!a.1, a.2)

@[simp] theorem Coef.flip_flip (a : Coef) : a.flip.flip = a := by
  rcases a with ⟨s, g⟩; simp [Coef.flip]

/-- Of a coefficient and its flip, one has the value 0 and the other has the value +1 or -1. -/
theorem Coef.val_flip (a : Coef) :
    (a.val = 0 ∧ (a.flip.val = 1 ∨ a.flip.val = -1)) ∨
    (a.flip.val = 0 ∧ (a.val = 1 ∨ a.val = -1)) := by
  rcases a with ⟨_ | _, _ | _⟩ <;> simp [Coef.flip, Coef.val]

/-- Uniform bits give the distribution of a coefficient: 0 for two of the four values, +1 for one,
-1 for one. -/
theorem Coef.cnt_val : cnt (fun c : Coef => c.val = 0) = 2 ∧ cnt (fun c : Coef => c.val = 1) = 1 ∧
    cnt (fun c : Coef => c.val = -1) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [cnt_eq_card_filter] <;> decide

/-! ## 2. Soundness: at most half, and 2^(-r) -/

/-- If an involution maps every value with the property P to one without it, at most half of the
values have P. -/
theorem two_mul_cnt_le {X : Type} [Fintype X] (P : X → Prop) (φ : X → X) (hφ : ∀ x, φ (φ x) = x)
    (h : ∀ x, P x → ¬ P (φ x)) : 2 * cnt P ≤ Fintype.card X := by
  classical
  have hle : cnt P ≤ cnt fun x => ¬ P x := by
    rw [cnt_eq_card_filter, cnt_eq_card_filter]
    apply card_le_card_of_injOn φ
    · intro x hx
      simpa using h x (by simpa using hx)
    · intro x _ y _ hxy
      simpa [hφ] using congrArg φ hxy
  have hsum := cnt_add_cnt_not P
  omega

/-- Independent draws: the tuples all of whose entries have the property P number (cnt P)^(number of
entries). -/
theorem cnt_forall {U X : Type} [Fintype U] [DecidableEq U] [Fintype X] (P : X → Prop) :
    cnt (fun F : U → X => ∀ u, P (F u)) = cnt P ^ Fintype.card U := by
  rw [cnt_forall_pi (A := fun _ : U => X) fun _ => P, prod_const, card_univ]

section Pass
variable {C : Type} [Fintype C] [DecidableEq C]

/-- At most half (one column of Ξ). Pass is any property of a vector of coefficients. If it never
holds both with 0 and with ±1 at the coordinate c₀, the other coefficients being the same, it holds
for at most half of the coefficient vectors. -/
theorem two_mul_cnt_pass_le (Pass : (C → ℤ) → Prop) (c₀ : C)
    (h : ∀ (cf : C → ℤ) (e : ℤ),
      e = 1 ∨ e = -1 → Pass (Function.update cf c₀ 0) → ¬ Pass (Function.update cf c₀ e)) :
    2 * cnt (fun ξ : C → Coef => Pass fun c => (ξ c).val) ≤ Fintype.card (C → Coef) := by
  apply two_mul_cnt_le _ (fun ξ => Function.update ξ c₀ (ξ c₀).flip)
  · intro ξ; simp
  · intro ξ h1 h2
    have e1 : (fun c => (ξ c).val) = Function.update (fun c => (ξ c).val) c₀ (ξ c₀).val := by simp
    have e2 : (fun c => (Function.update ξ c₀ (ξ c₀).flip c).val)
        = Function.update (fun c => (ξ c).val) c₀ (ξ c₀).flip.val := by
      funext c
      by_cases hc : c = c₀
      · subst hc; simp
      · rw [Function.update_of_ne hc, Function.update_of_ne hc]
    rw [e1] at h1
    rw [e2] at h2
    rcases Coef.val_flip (ξ c₀) with ⟨z0, z1⟩ | ⟨z0, z1⟩
    · rw [z0] at h1
      exact h _ _ z1 h1 h2
    · rw [z0] at h2
      exact h _ _ z1 h2 h1

/-- 2^(-r) (all columns of Ξ): under `h`, the fraction of the arrays of coefficients under which all
|U| independent tests pass is at most 2^(-|U|). -/
theorem cnt_forall_pass_mul_le {U : Type} [Fintype U] [DecidableEq U]
    (Pass : (C → ℤ) → Prop) (c₀ : C)
    (h : ∀ (cf : C → ℤ) (e : ℤ),
      e = 1 ∨ e = -1 → Pass (Function.update cf c₀ 0) → ¬ Pass (Function.update cf c₀ e)) :
    cnt (fun Ξ : U → C → Coef => ∀ u, Pass fun c => (Ξ u c).val) * 2 ^ Fintype.card U ≤
      Fintype.card (U → C → Coef) := by
  rw [cnt_forall (U := U) fun ξ : C → Coef => Pass fun c => (ξ c).val, ← mul_pow, Fintype.card_fun]
  exact Nat.pow_le_pow_left (by have := two_mul_cnt_pass_le Pass c₀ h; omega) _

/-- `cnt_forall_pass_mul_le` as a probability. -/
theorem pr_forall_pass_le {U : Type} [Fintype U] [DecidableEq U] (Pass : (C → ℤ) → Prop) (c₀ : C)
    (h : ∀ (cf : C → ℤ) (e : ℤ),
      e = 1 ∨ e = -1 → Pass (Function.update cf c₀ 0) → ¬ Pass (Function.update cf c₀ e)) :
    pr (unif (U → C → Coef)) {Ξ | ∀ u, Pass fun c => (Ξ u c).val} ≤ 1 / 2 ^ Fintype.card U := by
  have h1 := (pr_unif_le_div_iff (fun Ξ : U → C → Coef => ∀ u, Pass fun c => (Ξ u c).val) 1
      (2 ^ Fintype.card U) (by positivity)).2
    (by simpa using cnt_forall_pass_mul_le (U := U) Pass c₀ h)
  simpa using h1

theorem sum_update_mul (cf : C → ℤ) (c₀ : C) (x : ℤ) (a : C → ℤ) :
    ∑ c, Function.update cf c₀ x c * a c = x * a c₀ + ∑ c ∈ univ.erase c₀, cf c * a c := by
  rw [← add_sum_erase _ _ (mem_univ c₀)]
  congr 1
  · simp
  · exact sum_congr rfl fun c hc => by rw [Function.update_of_ne (ne_of_mem_erase hc)]

/-- The plain case: if one of the integers a is as large as the whole window, |a c₀| ≥ 2 t, the
combination Σ ξ a is in the window [-t, t) for at most half of the coefficient vectors. -/
theorem two_mul_cnt_inWindow_le (a : C → ℤ) (t : ℤ) (c₀ : C) (hbig : 2 * t ≤ |a c₀|) :
    2 * cnt (fun ξ : C → Coef => -t ≤ ∑ c, (ξ c).val * a c ∧ ∑ c, (ξ c).val * a c < t) ≤
      Fintype.card (C → Coef) := by
  refine two_mul_cnt_pass_le (fun cf => -t ≤ ∑ c, cf c * a c ∧ ∑ c, cf c * a c < t)
    c₀ fun cf e he h0 h1 => ?_
  simp only [sum_update_mul] at h0 h1
  have habs : |a c₀| < 2 * t := by
    rw [abs_lt]
    rcases he with rfl | rfl <;> constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  omega

end Pass

/-! ## 3. The window event: a tail bound -/

section Tail
open Real

/-- One term. The sum of exp (y ξ) over the four values of the two bits is 2 + 2 cosh y = 4 cosh²
(y/2) ≤ 4 exp (y²/4). -/
theorem sum_exp_coef_le (y : ℝ) : ∑ c : Coef, exp (y * (c.val : ℝ)) ≤ 4 * exp (y ^ 2 / 4) := by
  have h1 : ∑ c : Coef, exp (y * (c.val : ℝ)) = 2 + 2 * cosh y := by
    rw [show (univ : Finset Coef) =
        {(false, false), (false, true), (true, false), (true, true)} by decide]
    simp [Coef.val, cosh_eq]
    ring
  have h2 : 2 + 2 * cosh y = 4 * cosh (y / 2) ^ 2 := by
    have e := cosh_two_mul (y / 2)
    have e' := cosh_sq_sub_sinh_sq (y / 2)
    rw [show 2 * (y / 2) = y by ring] at e
    nlinarith
  have h3 : cosh (y / 2) ^ 2 ≤ exp (y ^ 2 / 4) := by
    have h := cosh_le_exp_half_sq (y / 2)
    have h0 : 0 ≤ cosh (y / 2) := (cosh_pos _).le
    calc cosh (y / 2) ^ 2 ≤ exp ((y / 2) ^ 2 / 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = exp (y ^ 2 / 4) := by
        rw [← exp_nat_mul]
        congr 1
        push_cast
        ring
  rw [h1, h2]
  linarith

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The combination Σ ξ a of the integers a with the coefficients ξ = (g c).val. -/
def comb (a : J → ℤ) (g : J → Coef) : ℤ := ∑ c, (g c).val * a c

/-- A bound on the moment generating function of a combination, as a sum over all coefficient
vectors. -/
theorem sum_exp_comb_le (a : J → ℤ) (l : ℝ) :
    ∑ g : J → Coef, exp (l * (comb a g : ℝ)) ≤
      4 ^ Fintype.card J * exp (l ^ 2 / 4 * ((∑ c, a c ^ 2 : ℤ) : ℝ)) := by
  have h1 : ∀ g : J → Coef,
      exp (l * (comb a g : ℝ)) = ∏ c, exp (l * (a c : ℝ) * ((g c).val : ℝ)) := by
    intro g
    rw [← exp_sum]
    congr 1
    unfold comb
    push_cast
    rw [mul_sum]
    exact sum_congr rfl fun c _ => by ring
  simp only [h1]
  rw [← Fintype.piFinset_univ,
    ← prod_univ_sum (fun _ => (univ : Finset Coef)) fun c x => exp (l * (a c : ℝ) * (x.val : ℝ))]
  calc ∏ c, ∑ x : Coef, exp (l * (a c : ℝ) * (x.val : ℝ)) ≤ ∏ c : J, 4 * exp ((l * (a c : ℝ)) ^ 2 / 4) :=
        prod_le_prod (fun c _ => sum_nonneg fun x _ => (exp_pos _).le) fun c _ => sum_exp_coef_le _
    _ = 4 ^ Fintype.card J * exp (l ^ 2 / 4 * ((∑ c, a c ^ 2 : ℤ) : ℝ)) := by
        rw [prod_mul_distrib, prod_const, card_univ, ← exp_sum]
        congr 2
        push_cast
        rw [mul_sum]
        exact sum_congr rfl fun c _ => by ring

theorem card_coefs : (Fintype.card (J → Coef) : ℝ) = 4 ^ Fintype.card J := by
  rw [Fintype.card_fun]
  simp

/-- The upper tail. For integers a with Σ a² ≤ V (V > 0, t ≥ 0), at most the fraction exp (-t²/V)
of the coefficient vectors give Σ ξ a ≥ t. -/
theorem cnt_tail_le (a : J → ℤ) (V t : ℝ) (hV : 0 < V)
    (ht : 0 ≤ t) (ha : ((∑ c, a c ^ 2 : ℤ) : ℝ) ≤ V) :
    (cnt (fun g : J → Coef => t ≤ (comb a g : ℝ)) : ℝ) ≤
      Fintype.card (J → Coef) * exp (-(t ^ 2 / V)) := by
  classical
  have hl : 0 ≤ 2 * t / V := by positivity
  have hm := sum_exp_comb_le a (2 * t / V)
  -- Markov's inequality
  have h1 : (cnt (fun g : J → Coef => t ≤ (comb a g : ℝ)) : ℝ) * exp (2 * t / V * t)
      ≤ ∑ g : J → Coef, exp (2 * t / V * (comb a g : ℝ)) := by
    rw [cnt_eq_card_filter, ← nsmul_eq_mul, ← sum_const]
    calc
      ∑ _g ∈ univ.filter (fun g : J → Coef => t ≤ (comb a g : ℝ)), exp (2 * t / V * t) ≤
          ∑ g ∈ univ.filter (fun g : J → Coef => t ≤ (comb a g : ℝ)),
            exp (2 * t / V * (comb a g : ℝ)) :=
          sum_le_sum fun g hg => exp_le_exp.2 (mul_le_mul_of_nonneg_left (mem_filter.1 hg).2 hl)
      _ ≤ ∑ g : J → Coef, exp (2 * t / V * (comb a g : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => (exp_pos _).le
  have h2 : exp ((2 * t / V) ^ 2 / 4 * ((∑ c, a c ^ 2 : ℤ) : ℝ)) ≤ exp (t ^ 2 / V) := by
    apply exp_le_exp.2
    calc (2 * t / V) ^ 2 / 4 * ((∑ c, a c ^ 2 : ℤ) : ℝ) ≤ (2 * t / V) ^ 2 / 4 * V :=
          mul_le_mul_of_nonneg_left ha (by positivity)
      _ = t ^ 2 / V := by field_simp; ring
  have e : exp (2 * t / V * t) = exp (t ^ 2 / V) * exp (t ^ 2 / V) := by
    rw [← exp_add]; congr 1; field_simp; ring
  have hpos := exp_pos (t ^ 2 / V)
  have h4 : (cnt (fun g : J → Coef => t ≤ (comb a g : ℝ)) : ℝ) * exp (t ^ 2 / V) * exp (t ^ 2 / V)
      ≤ 4 ^ Fintype.card J * exp (t ^ 2 / V) := by
    calc
      _ = (cnt (fun g : J → Coef => t ≤ (comb a g : ℝ)) : ℝ) * exp (2 * t / V * t) := by
        rw [e]; ring
      _ ≤ _ := h1.trans (hm.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
  have h3 : (cnt (fun g : J → Coef => t ≤ (comb a g : ℝ)) : ℝ) * exp (t ^ 2 / V) ≤
      4 ^ Fintype.card J :=
    le_of_mul_le_mul_right h4 hpos
  rw [card_coefs, exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact h3

omit [DecidableEq J] in
theorem comb_neg (a : J → ℤ) (g : J → Coef) : comb (fun c => -a c) g = -comb a g := by
  unfold comb; simp

/-- The window (one entry of Y Ξ). For integers a with Σ a² ≤ V (V > 0, t ≥ 0), the combination
Σ ξ a is outside [-t, t) for at most the fraction 2 exp (-t²/V) of the coefficient vectors. -/
theorem cnt_window_le (a : J → ℤ) (V : ℝ) (t : ℤ) (hV : 0 < V)
    (ht : 0 ≤ t) (ha : ((∑ c, a c ^ 2 : ℤ) : ℝ) ≤ V) :
    (cnt (fun g : J → Coef => ¬ (-t ≤ comb a g ∧ comb a g < t)) : ℝ) ≤
      Fintype.card (J → Coef) * (2 * exp (-((t : ℝ) ^ 2 / V))) := by
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 := cnt_tail_le a V t hV ht' ha
  have h2 := cnt_tail_le (fun c => -a c) V t hV ht' (by simpa using ha)
  have h3 : cnt (fun g : J → Coef => ¬ (-t ≤ comb a g ∧ comb a g < t)) ≤
      cnt (fun g : J → Coef => (t : ℝ) ≤ (comb a g : ℝ)) +
        cnt (fun g : J → Coef => (t : ℝ) ≤ (comb (fun c => -a c) g : ℝ)) := by
    refine cnt_le_add fun g hg => ?_
    rw [comb_neg]
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have c1 : comb a g < t := by exact_mod_cast hcon.1
    have c2 : -comb a g < t := by exact_mod_cast hcon.2
    exact hg ⟨by omega, c1⟩
  have h3' : (cnt (fun g : J → Coef => ¬ (-t ≤ comb a g ∧ comb a g < t)) : ℝ) ≤
      (cnt (fun g : J → Coef => (t : ℝ) ≤ (comb a g : ℝ)) : ℝ) +
        (cnt (fun g : J → Coef => (t : ℝ) ≤ (comb (fun c => -a c) g : ℝ)) : ℝ) := by
    exact_mod_cast h3
  linarith

/-- `cnt_window_le` as a probability. -/
theorem pr_window_le (a : J → ℤ) (V : ℝ) (t : ℤ) (hV : 0 < V)
    (ht : 0 ≤ t) (ha : ((∑ c, a c ^ 2 : ℤ) : ℝ) ≤ V) :
    pr (unif (J → Coef)) {g | ¬ (-t ≤ comb a g ∧ comb a g < t)} ≤
      ENNReal.ofReal (2 * exp (-((t : ℝ) ^ 2 / V))) := by
  rw [pr_unif_le_ofReal_iff _ (by positivity),
    div_le_iff₀ (by exact_mod_cast Fintype.card_pos), mul_comm]
  exact cnt_window_le a V t hV ht ha

/-- All entries of Y Ξ (one matrix). Y has the rows a i, each with Σ a² ≤ V, V > 0, and Ξ has the
columns Ξ u. For t ≥ 0 some entry leaves the window with probability at most (number of entries) ·
2 exp (-t²/V). -/
theorem pr_exists_window_le {I U : Type} [Fintype I] [Fintype U] [DecidableEq U] (a : I → J → ℤ)
    (V : ℝ) (t : ℤ) (hV : 0 < V) (ht : 0 ≤ t) (ha : ∀ i, ((∑ c, a i c ^ 2 : ℤ) : ℝ) ≤ V) :
    pr (unif (U → J → Coef))
        {Ξ | ∃ x : I × U, ¬ (-t ≤ comb (a x.1) (Ξ x.2) ∧ comb (a x.1) (Ξ x.2) < t)} ≤
      Fintype.card (I × U) * ENNReal.ofReal (2 * exp (-((t : ℝ) ^ 2 / V))) := by
  refine pr_exists_le_mul _ _ _ fun x => ?_
  have hm : (unif (U → J → Coef)).map (fun Ξ => Ξ x.2) = unif (J → Coef) :=
    map_eval_unif_pi (A := fun _ : U => J → Coef) x.2
  have := pr_window_le (a x.1) V t hV ht (ha x.1)
  rw [← hm, pr_map] at this
  exact this

omit [DecidableEq J] in
/-- A row of n entries, each of absolute value at most b, has Σ a² ≤ n b². -/
theorem sum_sq_le (a : J → ℤ) (b : ℤ) (hb : ∀ c, |a c| ≤ b) :
    ((∑ c, a c ^ 2 : ℤ) : ℝ) ≤ Fintype.card J * (b : ℝ) ^ 2 := by
  have h : ∑ c, a c ^ 2 ≤ ∑ _c : J, b ^ 2 := sum_le_sum fun c _ => by
    have := hb c
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  rw [sum_const, card_univ, nsmul_eq_mul] at h
  exact_mod_cast h

end Tail

/-! ## 4. The bound on the window event, for all matrices of a run -/

section Win
open Real

variable {Mx U : Type} [Fintype Mx] [DecidableEq Mx] [Fintype U] [DecidableEq U] {I J : Mx → Type}
  [∀ μ, Fintype (I μ)] [∀ μ, Fintype (J μ)] [∀ μ, DecidableEq (J μ)]

/-- The window event: an entry of some Y_μ Ξ_μ leaves the window [-t, t). -/
def Win (Y : ∀ μ, I μ → J μ → ℤ) (t : ℤ) (Ξ : ∀ μ, U → J μ → Coef) : Prop :=
  ∃ x : Σ μ, I μ × U,
    ¬ (-t ≤ comb (Y x.1 x.2.1) (Ξ x.1 x.2.2) ∧ comb (Y x.1 x.2.1) (Ξ x.1 x.2.2) < t)

/-- The window event. All cells have absolute value at most b > 0, no matrix has more than n₂ > 0
columns, and t ≥ 0. Then Pr[Win] ≤ n_Ψ · 2 exp (-t² / (n₂ b²)), where
n_Ψ is the number of entries of all the matrices Y_μ Ξ_μ. With t = 2^(β-1) and b = 2^7 this is 2 n_Ψ
exp (-2^(2β-2) / (2^14 n₂)). -/
theorem pr_win_le (Y : ∀ μ, I μ → J μ → ℤ) (b t : ℤ) (n₂ : ℕ) (hb : ∀ μ i c, |Y μ i c| ≤ b)
    (hb0 : 0 < b) (hn0 : 0 < n₂) (hn : ∀ μ, Fintype.card (J μ) ≤ n₂) (ht : 0 ≤ t) :
    pr (unif (∀ μ, U → J μ → Coef)) {Ξ | Win Y t Ξ} ≤
      Fintype.card (Σ μ, I μ × U) *
        ENNReal.ofReal (2 * exp (-((t : ℝ) ^ 2 / (n₂ * (b : ℝ) ^ 2)))) := by
  have hb0' : (0 : ℝ) < b := by exact_mod_cast hb0
  have hn0' : (0 : ℝ) < n₂ := by exact_mod_cast hn0
  refine pr_exists_le_mul _ _ _ fun x => ?_
  have hm1 : (unif (∀ μ, U → J μ → Coef)).map (fun Ξ => Ξ x.1) = unif (U → J x.1 → Coef) :=
    map_eval_unif_pi (A := fun μ => U → J μ → Coef) x.1
  have hm2 : (unif (U → J x.1 → Coef)).map (fun Ξ => Ξ x.2.2) = unif (J x.1 → Coef) :=
    map_eval_unif_pi (A := fun _ : U => J x.1 → Coef) x.2.2
  have hV : ((∑ c, Y x.1 x.2.1 c ^ 2 : ℤ) : ℝ) ≤ n₂ * (b : ℝ) ^ 2 :=
    (sum_sq_le _ b (hb x.1 x.2.1)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hn x.1) (by positivity))
  have := pr_window_le (Y x.1 x.2.1) (n₂ * (b : ℝ) ^ 2) t (by positivity) ht hV
  rw [← hm2, pr_map, ← hm1, pr_map] at this
  exact this

end Win

/-! ## 5. Numbers -/

section Numbers
open Real

/-- At β = 18 (t = 2^17), cells that are signed bytes (b = 2^7) and at most 2^13 columns, the
exponent is 128. -/
theorem ref_exponent :
    ((2 ^ 17 : ℤ) : ℝ) ^ 2 / (((2 ^ 13 : ℕ) : ℝ) * ((2 ^ 7 : ℤ) : ℝ) ^ 2) = 128 := by
  norm_num

theorem exp_neg_128_le : exp (-128) ≤ (2 : ℝ) ^ (-(184.66 : ℝ)) := by
  rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply exp_le_exp.2
  have := log_two_lt_d9
  linarith

/-- One entry: 2 e^(-128) ≤ 2^(-183.66). -/
theorem ref_entry : 2 * exp (-128) ≤ (2 : ℝ) ^ (-(183.66 : ℝ)) := by
  have h : (2 : ℝ) ^ (-(183.66 : ℝ)) = 2 * (2 : ℝ) ^ (-(184.66 : ℝ)) := by
    rw [show (-(183.66 : ℝ)) = 1 + -(184.66 : ℝ) by norm_num,
      rpow_add (by norm_num : (0 : ℝ) < 2), rpow_one]
  rw [h]
  exact mul_le_mul_of_nonneg_left exp_neg_128_le (by norm_num)

/-- The number of entries of a run at the reference parameters: 160 combinations for each of
9,035,776 rows. The theorem is an identity between numerals: it does not say that they are a
run's. (Of the three numbers of rows in it the first is m_Z of `ref_shapes`,
Inst/Model/FF/Index.lean, the third that of `mZ`, Inst/Model/Head/Index.lean.) -/
theorem ref_entries : 160 * (12 * 499712 + 12 * 221184 + 385024) = 1445724160 := by norm_num

set_option exponentiation.threshold 4000 in
theorem two_mul_ref_entries_le : (2 * 1445724160 : ℝ) ≤ (2 : ℝ) ^ (31.43 : ℝ) := by
  rw [rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : (100 : ℝ) * log 2891448320 ≤ 3143 * log 2 := by
    have h : log ((2891448320 : ℝ) ^ 100) ≤ log ((2 : ℝ) ^ 3143) :=
      log_le_log (by positivity) (by norm_num)
    rw [log_pow, log_pow] at h
    exact_mod_cast h
  calc (2 * 1445724160 : ℝ) = exp (log 2891448320) := by rw [exp_log (by norm_num)]; norm_num
    _ ≤ exp (log 2 * 31.43) := exp_le_exp.2 (by linarith)

/-- The bound of `pr_win_le` on ε_win, at the numerals of `ref_exponent` and `ref_entries`, is below
2^(-153.2). -/
theorem ref_eps_win : 1445724160 * (2 * exp (-128)) < (2 : ℝ) ^ (-(153.2 : ℝ)) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  calc 1445724160 * (2 * exp (-128)) = (2 * 1445724160) * exp (-128) := by ring
    _ ≤ (2 : ℝ) ^ (31.43 : ℝ) * (2 : ℝ) ^ (-(184.66 : ℝ)) :=
        mul_le_mul two_mul_ref_entries_le exp_neg_128_le (exp_pos _).le (rpow_nonneg h2.le _)
    _ = (2 : ℝ) ^ (-(153.23 : ℝ)) := by rw [← rpow_add h2]; norm_num
    _ < (2 : ℝ) ^ (-(153.2 : ℝ)) := rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)

end Numbers

end Prob
