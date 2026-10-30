-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gl/GlAgreeHalf.lean: the conclusion of `AgreeJ` (Cb/Gl/GlFinalAg.lean) is proved under the
further premise 2 e < d: agreement of Reed-Solomon codes within half the distance. Nothing assumed
beyond the hypotheses of its statement and whatever the arguments hold as proofs. Statements
(`Spec.half_rows`,
`Spec.half_count`, `Spec.bchksHalfAt`, `Spec.rsHalf_prox`, `Spec.rsHalf_group`, `Gl.Spec.agreeHalf`)
and proofs.
The three predicates under `GlJ` (`IsGlJ`, `IsGlS`: Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean)
do not ask a radius within half the distance: 2 e < d is a premise of its own in
`Gl.Spec.agreeHalf`. Within half the distance agreement of Reed-Solomon codes is proved in the
library (Code/Half.lean: `mca_rsCode`: at most n exceptional values, any number of rows), and the
own count of `Cb.BCHKS46At` (`bchksBound`, Cb/Gen/CodeListRS.lean) is at least n.
In standard terms: a Reed-Solomon code of length n and degree at most k has, at a radius e within
unique decoding (2 e + k + 1 ≤ n), mutual correlated agreement with at most n exceptional values,
for any number of rows (`Code.mca_rsCode`, Code/Half.lean); from this the file proves
`Gl.agreeHalf`, not `Gl.AgreeJ`. Main names (each statement under the hypotheses of its statement):
  `Spec.half_rows`: rows over E, distinct points in F, 2 e + k + 1 ≤ n: agreement, at most n
    exceptional values: in the form of `BCHKS46RowsAt` (Cb/Gen/CodeListRSAt.lean), by `OnRS`
    (Cb/Gen/CodeListRS.lean).
  `Spec.half_count`: 0 < k ≤ n: n ≤ bchksBound n k e (its number m is at least 3,
    the rate at most 1).
  `Spec.bchksHalfAt`: the body of `Cb.BCHKS46At F E`, word for word, with "2 e + k + 1 ≤ n" in the
    place of "n k < (n - e)²": a theorem.
  `Spec.rsHalf_prox`: distinct points, 0 < k < n: one code with encoder: lists by the proved Johnson
    bound, agreement with the count ⌊bchksBound n k e⌋, at the radii with 2 e + k + 1 ≤ n.
  `Spec.rsHalf_group`: distinct points, 0 < k a < n a, D ≤ mult a · (n a - k a): families under an
    even reading (`Reading.Even`, Cb/Gen/CodeRep.lean), at the radii below Johnson's as read with
    2 e < D.
  `Gl.Spec.agreeHalf`: `IsGlJ C d t e bad`, InJohnson |P| d e and 2 e < d give `C.MCArows e bad`.
`Gl.AgreeJ` (Cb/Gl/GlFinalAg.lean) is proved nowhere in this library: it follows from the statement
on codes `Cb.BCHKS46At Gl.F Gl.E` (`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean). The counts are those
of `Cb.BCHKS46At` (`bchksBound`), which this file does not prove: the predicates above
(`IsGlJ`, `IsGlS`, `IsGlCpJ`) are stated with them; the proved count (n a component) is far smaller.


Limits: this file says nothing at a radius not below half the distance (but for `Spec.half_count`,
which has no bound on e): `Cb.BCHKS46At F E` itself is neither proved nor used here.
This file does not say that any table of parameters lies within half: at the numbers of the copy's
file the radius lies beyond half the distance (reckoned by hand: lean/GAPS.md, (61)).


Terms: lean/GLOSSARY.md.

-/
import Cb.Gl.GlFinalAg
import Cb.Gen.CodeListRSAtProofs
import Code.Half

set_option autoImplicit false

namespace Cb
open Prob Blocks Polynomial
open CodeListRows CodeListRS CodeRep

namespace Spec

def half_rows : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] (n k e : ℕ) (x : Fin n → F), Function.Injective x → 2 * e + k + 1 ≤ n →
    ∀ (R : Type) [Finite R] (u₀ u₁ : R → Fin n → E),
      cnt (fun z : E => ∃ A : Finset (Fin n), n ≤ A.card + e ∧
        (∀ a, OnRS (fun j => algebraMap F E (x j)) k (fun j => u₀ a j + z * u₁ a j) A) ∧
          ¬ ((∀ a, OnRS (fun j => algebraMap F E (x j)) k (u₀ a) A) ∧ ∀ a, OnRS (fun j => algebraMap F E (x j)) k (u₁ a) A)) ≤ n

def half_count : Prop := ∀ n k e : ℕ, 0 < k → k ≤ n → (n : ℝ) ≤ bchksBound n k e

/-- The instances of the statement on codes within half the distance. -/
def bchksHalfAt : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] (n k e : ℕ) (x : Fin n → F),
    Function.Injective x → 0 < k → 0 < e → 2 * e + k + 1 ≤ n →
    ∀ u₀ u₁ : Fin n → E,
      (cnt (fun z : E =>
          ∃ A : Finset (Fin n),
            n ≤ A.card + e ∧
            OnRS (fun j => algebraMap F E (x j)) k (fun j => u₀ j + z * u₁ j) A ∧
            ¬ (OnRS (fun j => algebraMap F E (x j)) k u₀ A ∧
              OnRS (fun j => algebraMap F E (x j)) k u₁ A)) : ℝ) ≤ bchksBound n k e

def rsHalf_prox : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E]
      (n k msg r e₀ mca₀ : ℕ) (x : Fin n → F),
    Function.Injective x → 0 < k → k < n →
    (Code.RS.code x (k + 1) msg r e₀ mca₀).Prox E (fun e => 2 * e + k + 1 ≤ n)
      (fun e _ => listMax n (n - k) e) (fun e _ => ⌊bchksBound n k e⌋₊)

def rsHalf_group : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] (A : Type) [Fintype A]
      (n k msg r : A → ℕ) (x : ∀ a, Fin (n a) → F),
    (∀ a, Function.Injective (x a)) → (∀ a, 0 < k a) → (∀ a, k a < n a) →
    ∀ T : Reading (fun a => Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0), T.Even →
      ∀ D : ℕ, (∀ a, D ≤ T.mult a * (n a - k a)) →
        ∀ (R : A → Type) [∀ a, Finite (R a)], T.Prox E R
          (fun e => InJohnson (Fintype.card T.P) D e ∧ 2 * e < D)
          (fun e => listMax (Fintype.card T.P) D e)
          (fun e => ∑ a, ⌊bchksBound (n a) (k a) (e / T.mult a)⌋₊)

end Spec

/-- "Agrees on A with a polynomial of degree at most k", said by `OnRS` (Cb/Gen/CodeListRS.lean) and
by `Code.agreeOn` (Code/Agree.lean) at `Code.rsCode` (Code/Half.lean): for distinct points (`hx`)
the two are equivalent. -/
theorem half_onRS {K : Type} [Field K] {n : ℕ} (x : Fin n → K) (hx : Function.Injective x) (k : ℕ)
    (u : Fin n → K) (A : Finset (Fin n)) :
    OnRS x k u A ↔ u ∈ Code.agreeOn (Code.rsCode ⟨x, hx⟩ k) A := by
  constructor
  · rintro ⟨p, hp, h⟩
    refine ⟨fun j => p.eval (x j), ⟨p, ?_, fun _ => rfl⟩, h⟩
    by_cases h0 : p = 0
    · rw [h0, natDegree_zero]; exact Nat.zero_le _
    · exact Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt h0).mpr hp)
  · rintro ⟨w, ⟨p, hp, hw⟩, h⟩
    exact ⟨p, lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hp),
      fun j hj => (h j hj).trans (hw j)⟩

theorem half_rows : Spec.half_rows := by
  intro F E _ _ _ _ n k e x hx hh R _ u₀ u₁
  have hxE : Function.Injective (fun j => algebraMap F E (x j)) :=
    (algebraMap F E).injective.comp hx
  have h := Code.mca_rsCode (L := E) (ι := Fin n) ⟨_, hxE⟩ (e := e) (K := k)
    (by rw [Fintype.card_fin]; exact hh) R u₀ u₁
  simp only [Fintype.card_fin] at h
  refine le_trans (cnt_mono fun z hz => ?_) h
  obtain ⟨A, hA, h1, h2⟩ := hz
  exact ⟨A, hA,
    fun a => (half_onRS _ hxE _ _ _).1 (h1 a),
    fun hc =>
      h2 ⟨fun a => (half_onRS _ hxE _ _ _).2 (hc.1 a), fun a => (half_onRS _ hxE _ _ _).2 (hc.2 a)⟩⟩

theorem half_count : Spec.half_count := by
  intro n k e hk hkn
  unfold bchksBound
  have hM3 : (3 : ℝ) ≤ bchksM n k e := le_max_right _ _
  generalize bchksM n k e = M at hM3 ⊢
  have hn : (0 : ℝ) < n := by exact_mod_cast lt_of_lt_of_le hk hkn
  have hρ0 : (0 : ℝ) < (k : ℝ) / n := div_pos (by exact_mod_cast hk) hn
  have hρ1 : (k : ℝ) / n ≤ 1 := (div_le_one hn).2 (by exact_mod_cast hkn)
  have hγ : (0 : ℝ) ≤ (e : ℝ) / n := div_nonneg (Nat.cast_nonneg _) hn.le
  generalize (k : ℝ) / n = ρ at hρ0 hρ1 ⊢
  generalize (e : ℝ) / n = γ at hγ ⊢
  have hs0 : 0 < Real.sqrt ρ := Real.sqrt_pos.2 hρ0
  have hs1 : Real.sqrt ρ ≤ 1 := Real.sqrt_le_one.2 hρ1
  generalize Real.sqrt ρ = s at hs0 hs1 ⊢
  have hM0 : (0 : ℝ) < M + 1 / 2 := by linarith
  have hden : 0 < 3 * (ρ * s) := by positivity
  have hden3 : 3 * (ρ * s) ≤ 3 := by nlinarith [mul_le_one₀ hρ1 hs0.le hs1]
  have h5 : ((7 : ℝ) / 2) ^ 5 ≤ (M + 1 / 2) ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
  have hx : (0 : ℝ) ≤ 3 * (M + 1 / 2) * γ * ρ := by positivity
  have hnum : (3 : ℝ) ≤ 2 * (M + 1 / 2) ^ 5 + 3 * (M + 1 / 2) * γ * ρ := by
    have : ((7 : ℝ) / 2) ^ 5 = 16807 / 32 := by norm_num
    linarith
  have hfr : (1 : ℝ) ≤ (2 * (M + 1 / 2) ^ 5 + 3 * (M + 1 / 2) * γ * ρ) / (3 * (ρ * s)) :=
    (one_le_div hden).2 (le_trans hden3 hnum)
  have h2 : (0 : ℝ) ≤ (M + 1 / 2) / s := div_nonneg hM0.le hs0.le
  nlinarith [mul_le_mul_of_nonneg_right hfr hn.le]

theorem bchksHalfAt : Spec.bchksHalfAt := by
  intro F E _ _ _ _ n k e x hx hk _ hh u₀ u₁
  refine le_trans
    (Nat.cast_le.2
      (le_trans (cnt_mono fun z hz => ?_)
        (half_rows F E n k e x hx hh Unit (fun _ => u₀) (fun _ => u₁))))
    (half_count n k e hk (by omega))
  obtain ⟨A, hA, h1, h2⟩ := hz
  exact ⟨A, hA, fun _ => h1, fun hc => h2 ⟨hc.1 (), hc.2 ()⟩⟩

theorem rsHalf_prox : Spec.rsHalf_prox := by
  intro F E _ _ _ _ n k msg r e₀ mca₀ x hx hk hkn
  refine ⟨fun e he R _ f => ?_, fun e he R _ f₀ f₁ => ?_⟩
  · have h := johnson_enc F E (Code.RS.code x (k + 1) msg r e₀ mca₀) e (Code.RS.code_dist hx hkn)
      (by
        show InJohnson n (n - (k + 1) + 1) e
        rw [dist_eq hkn]
        exact inJohnson_of_unique n (n - k) e (Nat.sub_le _ _) (by omega)) R f
    have h' : cnt (fun M => DecodesTo ((Code.RS.code x (k + 1) msg r e₀ mca₀).GE E) e f M) ≤
        listMax n (n - (k + 1) + 1) e := h
    rwa [dist_eq hkn] at h'
  · have h := half_rows F E n k e x hx he R f₀ f₁
    refine Nat.le_floor
      (le_trans
        (Nat.cast_le.mpr (le_trans (le_of_eq (cnt_congr fun θ => exists_congr fun S => ?_)) h))
        (half_count n k e hk hkn.le))
    rw [CodeListRS.onCode_iff, CodeListRS.onCode_iff, CodeListRS.onCode_iff]
    exact Iff.rfl

theorem rsHalf_group : Spec.rsHalf_group := by
  intro F E _ _ _ _ A _ n k msg r x hx hk hkn T hT D hD R _
  have hd : ∀ a, HasDist (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).G
      (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d :=
    fun a => Code.RS.code_dist (hx a) (hkn a)
  have hD' : ∀ a, D ≤ T.mult a * (Code.RS.code (x a) (k a + 1) (msg a) (r a) 0 0).d := fun a => by
    show D ≤ T.mult a * (n a - (k a + 1) + 1)
    rw [dist_eq (hkn a)]
    exact hD a
  have hP := prox_johnson_of_comps F E A _ T hT hd D hD' R _ _ _ fun a =>
    rsHalf_prox F E (n a) (k a) (msg a) (r a) 0 0 (x a) (hx a) (hk a) (hkn a)
  have hok : ∀ e, (InJohnson (Fintype.card T.P) D e ∧ 2 * e < D) →
      InJohnson (Fintype.card T.P) D e ∧ ∀ a, 2 * (e / T.mult a) + k a + 1 ≤ n a := by
    intro e he
    refine ⟨he.1, fun a => ?_⟩
    have h1 : e / T.mult a * T.mult a ≤ e := Nat.div_mul_le_self e (T.mult a)
    have h2 := hD a
    have h3 : T.mult a * (2 * (e / T.mult a)) < T.mult a * (n a - k a) := by nlinarith [he.2]
    have h4 := Nat.lt_of_mul_lt_mul_left h3
    have := hkn a
    omega
  exact ⟨fun e he => hP.list e (hok e he), fun e he => hP.mca e (hok e he)⟩

namespace Gl

/-- States the conclusion of `AgreeJ` (Cb/Gl/GlFinalAg.lean) under the further premise 2 e < d:
agreement of Reed-Solomon codes within half the distance; `agreeHalf` proves it; `AgreeJ` itself is
proved nowhere in this library. -/
def Spec.agreeHalf : Prop := ∀ (P : Type) [Fintype P] (C : LdCode E P) (d t e bad : ℕ),
    IsGlJ C d t e bad → InJohnson (Fintype.card P) d e → 2 * e < d → C.MCArows e bad

theorem agreeHalf : Spec.agreeHalf := by
  intro P _ C d t e bad h hJ hh
  obtain ⟨A, iA, dA, a, k, msg, r, pos, mult, R, fR, dR, rfl, ha, hk0, hk, hp, hE, hd, -, hm, hb⟩ :=
    h
  exact ld_rows_mono E P _ _ _ _ hb
    (ld_rows_ld F E A (grp a k msg r) (⟨P, pos, mult⟩ : Reading (grp a k msg r)) _ _ hp
      (fun R' _ _ =>
        (rsHalf_group F E A (fun i => 2 ^ a i) k msg r (fun i => pts (a i))
            (fun i => gl_pts_inj (a i) (ha i)) hk0 hk
            (⟨P, pos, mult⟩ : Reading (grp a k msg r)) hE _ hd R').mca
          _ ⟨hJ, hh⟩) R)

end Gl
end Cb
