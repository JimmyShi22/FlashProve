-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSumCubeProofs.lean: the proofs of Cb/Req/ReqSumCube.lean. Many statements of this library
are written twice: a definition in the namespace `Spec` states a proposition, and a theorem of the
same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Req/ReqSumCube.lean):
  `ext_mle`, `ext_nat`: `Blocks.ext` of a numbered vector = `Alg.mle` of the same vector on
    vertices.
  `wsum_split`, `wsum_all`: the weighted sum over a cube (weights `wts v γ`) = an extension at γ
    (`wsum_split`: for n = v + w).
  `vtx_num`: the 0/1 point of the number of a vertex.
  `wts_ne`: `∀ i : Fin n, wts ve γ i true ≠ 0` ↔ `∀ t < ve, γ t ≠ 0`, for ve ≤ n.

Notation: `n`, `v`, `w`: natural numbers, numbers of variables ("The weighted sum over v + w
variables.": `Spec.wsum_split`, Cb/Req/ReqSumCube.lean); `γ`: a function ℕ → E; `wts ve γ`
(Cb/Req/ReqSumCube.lean): the weights: the equality factor at γ on the variables t < ve, plain on
the others; `Blocks.ext` (Blocks/Ext.lean), `Alg.mle` (Alg/Mle.lean): the multilinear extension.

Limits: what the head of Cb/Req/ReqSumCube.lean lists as not said is not said here either.
-/
import Cb.Req.ReqSumCube

set_option autoImplicit false

namespace Cb.Req
open Blocks Alg Finset

theorem ext_mle : Spec.ext_mle := by
  intro E _ v f pt
  unfold Blocks.ext
  simp only [eqN_eq, Nat.zero_add]
  exact mleN_eq_mle f _

theorem ext_nat : Spec.ext_nat := by
  intro E _ v f z
  rw [ext_mle]
  congr 1
  funext t
  simp [nat, t.2]

theorem vtx_num : Spec.vtx_num := by
  intro E _ v b
  funext t
  by_cases ht : t < v
  · have h := congrFun (bits_num b) ⟨t, ht⟩
    have h' : (num b).testBit (v - 1 - t) = b ⟨t, ht⟩ := h
    simp [vtx, nat, corner, ht, h']
  · simp [vtx, nat, ht]

/-- the high bits of a number a · 2^w + j -/
theorem bits_high (v w a : ℕ) {j : ℕ} (hj : j < 2 ^ w) (i : Fin v) :
    bits (v + w) (a * 2 ^ w + j) (Fin.castAdd w i) = bits v a i := by
  have hi := i.2
  unfold bits
  rw [mul_comm a, Nat.testBit_two_pow_mul_add a hj, Fin.val_castAdd, if_neg (by omega)]
  congr 1
  omega

theorem wsum_split : Spec.wsum_split := by
  intro E _ n v w γ g hn
  subst hn
  have h1 : ∀ b : Fin (v + w) → Bool, (∏ i, wts v γ i (b i)) * g (num b) =
      (fun c => (∏ i, wts v γ i (bits (v + w) c i)) * g c) (num b) := fun b => by
    show _ = (∏ i, wts v γ i (bits (v + w) (num b) i)) * g (num b)
    rw [bits_num]
  rw [Finset.sum_congr rfl fun b _ => h1 b,
    sum_num (fun c => (∏ i, wts v γ i (bits (v + w) c i)) * g c), pow_add, sum_range_mul_add]
  unfold Blocks.ext
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  rw [Fin.prod_univ_add]
  have h2 : ∏ i : Fin w, wts v γ (Fin.natAdd v i) (bits (v + w) (a * 2 ^ w + j) (Fin.natAdd v i)) =
      1 :=
    Finset.prod_eq_one fun i _ => by simp [wts]
  rw [h2, mul_one, eqN_eq]
  unfold Alg.eqN eqk
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [bits_high v w a (Finset.mem_range.1 hj) i]
  simp [wts, i.2]

theorem wsum_all : Spec.wsum_all := by
  intro E _ v γ g
  rw [wsum_split E v v 0 γ g rfl]
  simp

theorem wts_ne : Spec.wts_ne := by
  intro E _ n ve γ hle
  constructor
  · intro h t ht
    have := h ⟨t, lt_of_lt_of_le ht hle⟩
    simpa [wts, ht] using this
  · intro h i
    by_cases hi : i.val < ve
    · simpa [wts, hi] using h i.val hi
    · simp [wts, hi]

end Cb.Req
