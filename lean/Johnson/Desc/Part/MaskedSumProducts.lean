-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumProducts.lean: what a caller of the masked sumcheck owes for a product of
two multilinear extensions, paid over the part's OWN variables (Johnson/Desc/Part/MaskedSum4.lean's
`Var`). Statements and proofs.

  `two_point`, `two_plain`: a variable read in K (`Var.wt`, MaskedSumSound.lean) is a two-point
  weight
    (OnBytes/Desc/First/P1/SumMle.lean): summed at z: (1 - z, z); summed plainly: (1, 1).
  `weightsOf`, `twos_wt`: so for a list of variables, each with at least k coefficients.
  `isSum_product`: for a call with ends whose variables all have at least three coefficients and
    whose further variable has three (dY = 2): the summand
      S (x ++ [Y]) = (A x + Y m0) (B x + Y m1),
    A x and B x the extensions of two tables at the challenges x, IS SUMMED, over the call's
    variables
    with Y last, TO the sum over the cube, under the variables' weights, of A b * B b. This is the
    premise `hS` of `sound_hear` at such a caller.

A table's first bit belongs to the variable that the first round sums.
-/
import Johnson.Desc.Part.MaskedSumSound
import OnBytes.Desc.First.P1.PscProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K] (ρ : Reading K)

theorem two_point (z : E) (d : ℕ) (hd : 1 ≤ d) :
    ((Var.point z d).wt ρ).Two (1 - ρ.val z) (ρ.val z) :=
  two_of_moments _ 1 (ρ.val z) hd rfl fun _ _ => rfl

theorem two_plain' (d : ℕ) (hd : 1 ≤ d) : ((Var.plain d).wt ρ).Two 1 1 := by
  have h := two_of_moments ((Var.plain d).wt ρ) 2 1 hd rfl fun _ _ => rfl
  have e : (2 : K) - 1 = 1 := by norm_num
  rw [e] at h
  exact h

/-- A variable's two weights. -/
def Var.two : Var → K × K
  | .plain _ => (1, 1)
  | .point z _ => (1 - ρ.val z, ρ.val z)

/-- The variables' weights. -/
def weightsOf (vs : List Var) : List (K × K) := vs.map (Var.two ρ)

theorem twos_wt (k : ℕ) (hk : 1 ≤ k) : ∀ vs : List Var, (∀ v ∈ vs, k ≤ v.d) →
    Twos k (vs.map (Var.wt ρ)) (weightsOf ρ vs)
  | [], _ => trivial
  | v :: vs, h => by
    have hv : k ≤ v.d := h v (by simp)
    refine ⟨?_, by rw [Var.wt_d]; exact hv, twos_wt k hk vs fun u hu => h u (by simp [hu])⟩
    cases v with
    | plain d => exact two_plain' ρ d (le_trans hk hv)
    | point z d => exact two_point ρ z d (le_trans hk hv)

/-- **The premise hS of sound_hear, for a product of two extensions with shown end values.** -/
theorem isSum_product (lead : Nat) (vs : List Var) (n : Nat) (h3 : ∀ v ∈ vs, 3 ≤ v.d)
    (A B : List Bool → K) (m0 m1 : K) :
    IsSum ((⟨lead, vs, some ⟨2, n⟩⟩ : Call).all.map (Var.wt ρ))
      (fun rs => mle (vs.length + 1) (ext1 vs.length A m0) rs *
        mle (vs.length + 1) (ext1 vs.length B m1) rs)
      (tot (weightsOf ρ vs) fun b => A b * B b) := by
  have hall : (⟨lead, vs, some ⟨2, n⟩⟩ : Call).all = vs ++ [Var.point zeroE 3] := rfl
  have h3' : ∀ v ∈ vs ++ [Var.point zeroE 3], 3 ≤ v.d := by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact h3 v h
    · rw [List.mem_singleton] at h
      rw [h]
      exact le_refl 3
  have ht := twos_wt ρ 3 (by omega) (vs ++ [Var.point zeroE 3]) h3'
  have hs := isSum_mul _ _ (ext1 vs.length A m0) (ext1 vs.length B m1) ht
  have hl : ((vs ++ [Var.point zeroE 3]).map (Var.wt ρ)).length = vs.length + 1 := by simp
  rw [hl] at hs
  rw [hall]
  refine hs.congr (fun _ => rfl) ?_
  have hw : weightsOf ρ (vs ++ [Var.point zeroE 3]) = weightsOf ρ vs ++ [(1, 0)] := by
    unfold weightsOf
    rw [List.map_append]
    show _ ++ [((1 : K) - ρ.val zeroE, ρ.val zeroE)] = _
    rw [ρ.zero, sub_zero]
  have hlen : (weightsOf ρ vs).length = vs.length := by simp [weightsOf]
  rw [hw, ← hlen]
  exact tot_ext1_mul (weightsOf ρ vs) A B m0 m1

/-- At the challenges x with beta behind them the summand is (A x + beta m0) (B x + beta m1). -/
theorem product_at (n : ℕ) (A B : List Bool → K) (m0 m1 : K) (x : List K) (beta : K)
    (hx : x.length = n) :
    mle (n + 1) (ext1 n A m0) (x ++ [beta]) * mle (n + 1) (ext1 n B m1) (x ++ [beta]) =
      (mle n A x + beta * m0) * (mle n B x + beta * m1) := by
  rw [mle_ext1 n A m0 x beta hx, mle_ext1 n B m1 x beta hx]

end VerifiableInference.Desc.Part.MaskedSum
