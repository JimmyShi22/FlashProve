-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeListRSProofs.lean: the proofs of those statements of Cb/Gen/CodeListRS.lean that start
from `BCHKS46Rows` (tables), and of `Spec.bchks46_of_rows`.

`Spec.rows_cost_nothing` and what follows from it are in Cb/Gen/CodeListRows.lean.
Nothing is assumed beyond the hypotheses of the statements: `BCHKS46Rows` is a hypothesis in the
text of each statement.
Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeListRS
import Cb.Gen.CodeListProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks Polynomial

namespace CodeListRS

/-- Agreement with a polynomial of degree at most k is agreement with the image of a vector of
k + 1 coefficients. -/
theorem onRS_iff {K : Type} [Field K] {n : ℕ} (x : Fin n → K) (k : ℕ)
    (u : Fin n → K) (A : Finset (Fin n)) :
    OnRS x k u A ↔
    ∃ v : Fin (k + 1) → K, ∀ j ∈ A, u j = Code.RS.gen x (fun i : Fin (k + 1) => (i : ℕ)) v j := by
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨fun i => p.coeff i, fun j hj => by rw [Code.RS.gen_coeff hp, h j hj]⟩
  · rintro ⟨v, h⟩
    exact ⟨Code.RS.poly (fun i : Fin (k + 1) => (i : ℕ)) v, Code.RS.degree_poly_lt (fun i => i.2) v,
      fun j hj => by rw [h j hj, Code.RS.gen_eq_eval]⟩

variable {F E : Type} [Field F] [Field E] [Algebra F E] {n : ℕ}

/-- The generator of `Code.RS.code` over E acts as the generator at the points read in E. -/
theorem code_GE_mulVec (x : Fin n → F) (k msg r e mca : ℕ) (v : Fin k → E) (j : Fin n) :
    ((Code.RS.code x k msg r e mca).GE E).mulVec v j =
      Code.RS.gen (fun j => algebraMap F E (x j)) (fun i : Fin k => (i : ℕ)) v j := by
  rw [Code.RS.code_GE]
  exact Code.RS.code_mulVec (fun j => algebraMap F E (x j)) k msg r e mca v j

/-- "On the code" of the interface (`Code.Enc.OnCode`), for `Code.RS.code` of dimension k + 1:
every row agrees with a polynomial of degree at most k. -/
theorem onCode_iff (x : Fin n → F) (k msg r e mca : ℕ) {R : Type}
    (f : R → Fin n → E) (S : Finset (Fin n)) :
    (Code.RS.code x (k + 1) msg r e mca).OnCode E f S ↔
    ∀ a, OnRS (fun j => algebraMap F E (x j)) k (f a) S := by
  constructor
  · rintro ⟨M, hM⟩ a
    exact (onRS_iff _ k (f a) S).mpr
      ⟨M a, fun j hj => (hM j hj a).trans (code_GE_mulVec x (k + 1) msg r e mca (M a) j)⟩
  · intro h
    choose M hM using fun a => (onRS_iff _ k (f a) S).mp (h a)
    exact ⟨M, fun j hj a => (hM a j hj).trans (code_GE_mulVec x (k + 1) msg r e mca (M a) j).symm⟩

/-- Below the Johnson radius in the notation of `BCHKS46` (Cb/Gen/CodeListRS.lean),
n k < (n - e)^2: then k < n, and `InJohnson` holds for the code's distance n - k
(`inJohnson_of_radius`). -/
theorem lt_of_radius {n k e : ℕ} (h : n * k < (n - e) ^ 2) : k < n := by
  have h1 : (n - e) ^ 2 ≤ n * n := by
    rw [← sq]
    exact Nat.pow_le_pow_left (Nat.sub_le n e) 2
  exact Nat.lt_of_mul_lt_mul_left (lt_of_lt_of_le h h1)

theorem dist_eq {n k : ℕ} (h : k < n) : n - (k + 1) + 1 = n - k := by omega

theorem inJohnson_of_radius {n k e : ℕ} (h : n * k < (n - e) ^ 2) : InJohnson n (n - k) e := by
  have hk := lt_of_radius h
  unfold InJohnson
  rwa [Nat.sub_sub_self hk.le]

end CodeListRS

open CodeListRS

-- Limit: the statement has the premise `Cb.BCHKS46Rows`, the statement on codes `Cb.BCHKS46` for
-- tables of rows: this file does not prove either.
theorem bchks46_of_rows : Spec.bchks46_of_rows := by
  intro H K _ _ n k e x hx hk he hJ u₀ u₁
  refine le_trans (Nat.cast_le.mpr (le_of_eq (cnt_congr fun z => exists_congr fun A => ?_)))
    (H K n k e x hx hk he hJ Unit (fun _ => u₀) (fun _ => u₁))
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun _ => h2, fun h => h3 ⟨h.1 (), h.2 ()⟩⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2 (), fun h => h3 ⟨fun _ => h.1, fun _ => h.2⟩⟩⟩

-- Limit: the statement has the premise `Cb.BCHKS46Rows`, the statement on codes `Cb.BCHKS46` for
-- tables of rows: this file does not prove either.
theorem rs_mcaAt_of_rows : Spec.rs_mcaAt_of_rows := by
  intro H F E _ _ _ _ n k msg r e₀ mca₀ x hx e hk he hJ R _ f₀ f₁
  have h :=
    H E n k e (fun j => algebraMap F E (x j)) ((algebraMap F E).injective.comp hx) hk he hJ R f₀ f₁
  refine Nat.le_floor
    (le_trans (Nat.cast_le.mpr (le_of_eq (cnt_congr fun θ => exists_congr fun S => ?_))) h)
  rw [onCode_iff, onCode_iff, onCode_iff]
  exact Iff.rfl

-- Limit: the statement has the premise `Cb.BCHKS46Rows`, the statement on codes `Cb.BCHKS46` for
-- tables of rows: this file does not prove either.
theorem rs_prox_of_rows : Spec.rs_prox_of_rows := by
  intro H F E _ _ _ _ n k msg r e₀ mca₀ x hx hk
  refine ⟨fun e he R _ f => ?_,
    fun e he R _ => rs_mcaAt_of_rows H F E n k msg r e₀ mca₀ x hx e hk he.1 he.2 R⟩
  have hkn := lt_of_radius he.2
  have h := johnson_enc F E (Code.RS.code x (k + 1) msg r e₀ mca₀) e (Code.RS.code_dist hx hkn)
    (by
      show InJohnson n (n - (k + 1) + 1) e
      rw [dist_eq hkn]
      exact inJohnson_of_radius he.2) R f
  have h' : cnt (fun M => DecodesTo ((Code.RS.code x (k + 1) msg r e₀ mca₀).GE E) e f M) ≤
      listMax n (n - (k + 1) + 1) e := h
  rwa [dist_eq hkn] at h'

-- Limit: the statement has the premise `Cb.BCHKS46Rows`, the statement on codes `Cb.BCHKS46` for
-- tables of rows: this file does not prove either.
theorem rs_listProps_of_rows : Spec.rs_listProps_of_rows := by
  intro H F E _ _ _ _ _ n k msg r e x hx hx0 hp hk he hJ
  have hkn := lt_of_radius hJ
  have hcore : (Code.RS.code x (k + 1) msg r e ⌊bchksBound n k e⌋₊).Core :=
    { place := hp
      dist := Code.RS.code_dist hx hkn
      pos := Nat.succ_pos _
      hides := ((Code.RS.code x (k + 1) msg r e ⌊bchksBound n k e⌋₊).hides_iff_ontoUpTo r).2
        (Code.RS.code_ontoUpTo hx hx0 hp) }
  have hP := rs_prox_of_rows H F E n k msg r e ⌊bchksBound n k e⌋₊ x hx hk
  exact listProps_of_prox F E _ _ _ _ e (listMax n (n - k) e) ⌊bchksBound n k e⌋₊ hcore hP ⟨he, hJ⟩
    (fun _ => le_rfl) (fun _ => le_rfl)

end Cb
