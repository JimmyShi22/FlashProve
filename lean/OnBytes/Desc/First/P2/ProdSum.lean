--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P2/ProdSum.lean: what a level of the grand product owes to the masked sumcheck's
law. `isSum_level`: the level's summand, with the further variable Y last, is summed by the level's
variables, in any order of the bits, to the map above at the point z, through polynomials with
three coefficients. Algebra over a field alone. Definitions, statements and proofs.

How. `psum`: the sum over the coordinates that are still to come, as a function of the point so
far. `psum_quad`: it is a polynomial with three coefficients in a coordinate that is not among
them. `isSum_summand`: so the summand is summed to psum. `psum_congr_cube`: psum reads its function
on the cube alone (at the coordinates summed), where the product of the two halves is the map
above. `psum_affine`: of a map that is affine in each coordinate, psum is the value at z.

Limits. The variables are letters: any records with `SumsAt`. It has no error term: an identity of
sums.
Not claimed: anything on probabilities, on an honest prover or on hiding.

-/
import OnBytes.Desc.First.P2.ProdCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P2
open Polynomial
open OnBytes.Desc.First.P1

variable {K : Type} [Field K]

/-- G is a polynomial with three coefficients in each of the first m coordinates. -/
def QuadIn (m : ℕ) (G : (ℕ → K) → K) : Prop :=
  ∀ (x : ℕ → K) (i : ℕ), i < m →
    ∃ q : K[X], q.natDegree < 3 ∧ ∀ c, q.eval c = G (Function.update x i c)

/-- The sum of G over the coordinates L, each with the equality weights at its coordinate of z. -/
def psum (z : ℕ → K) (G : (ℕ → K) → K) : List ℕ → (ℕ → K) → K
  | [], x => G x
  | i :: L, x =>
    (1 - z i) * psum z G L (Function.update x i 0) + z i * psum z G L (Function.update x i 1)

theorem psum_quad {m : ℕ} (z : ℕ → K) {G : (ℕ → K) → K} (hG : QuadIn m G) {i : ℕ} (hi : i < m) :
    ∀ (L : List ℕ) (x : ℕ → K), i ∉ L →
      ∃ q : K[X], q.natDegree < 3 ∧ ∀ c, q.eval c = psum z G L (Function.update x i c)
  | [], x, _ => hG x i hi
  | j :: L, x, h => by
    have hij : i ≠ j := fun e => h (by simp [e])
    have hL : i ∉ L := fun e => h (by simp [e])
    obtain ⟨q0, d0, e0⟩ := psum_quad z hG hi L (Function.update x j 0) hL
    obtain ⟨q1, d1, e1⟩ := psum_quad z hG hi L (Function.update x j 1) hL
    refine ⟨C (1 - z j) * q0 + C (z j) * q1, ?_, fun c => ?_⟩
    · exact lt_of_le_of_lt (natDegree_add_le _ _)
        (max_lt (lt_of_le_of_lt (natDegree_C_mul_le _ _) d0)
          (lt_of_le_of_lt (natDegree_C_mul_le _ _) d1))
    · rw [eval_add, eval_mul, eval_mul, eval_C, eval_C, e0, e1]
      show _ = (1 - z j) * psum z G L (Function.update (Function.update x i c) j 0) +
        z j * psum z G L (Function.update (Function.update x i c) j 1)
      rw [Function.update_comm hij c 0 x, Function.update_comm hij c 1 x]

/-- The summand is summed to psum. -/
theorem isSum_summand {m : ℕ} (z : ℕ → K) (wt : ℕ → Wt K) (wY : Wt K)
    (hw : ∀ i, SumsAt (wt i) (z i)) (hwY : SumsAt wY 0) (GY : (ℕ → K) → K → K)
    (hY : ∀ x, ∃ q : K[X], q.natDegree < 3 ∧ ∀ y, q.eval y = GY x y)
    (hG : QuadIn m fun x => GY x 0) :
    ∀ (L : List ℕ) (x : ℕ → K), L.Nodup → (∀ i ∈ L, i < m) →
      IsSum (L.map wt ++ [wY]) (summand GY L x) (psum z (fun x => GY x 0) L x)
  | [], x, _, _ => by
    obtain ⟨q, hd, hq⟩ := hY x
    show IsSum [wY] _ _
    refine ⟨q, by rw [hwY.1]; exact hd, ?_, fun y => ?_⟩
    · rw [hwY.2 q hd, hq 0]
      show (1 - 0) * GY x 0 + 0 * q.eval 1 = GY x 0
      ring
    · exact (hq y).symm
  | i :: L, x, hn, hm => by
    have hiL : i ∉ L := (List.nodup_cons.mp hn).1
    have hL : L.Nodup := (List.nodup_cons.mp hn).2
    have hi : i < m := hm i (by simp)
    obtain ⟨q, hd, hq⟩ := psum_quad z hG hi L x hiL
    show IsSum (wt i :: (L.map wt ++ [wY])) _ _
    refine ⟨q, by rw [(hw i).1]; exact hd, ?_, fun c => ?_⟩
    · rw [(hw i).2 q hd, hq 0, hq 1]
      rfl
    · rw [hq c]
      exact isSum_summand z wt wY hw hwY GY hY hG L (Function.update x i c) hL
        fun k hk => hm k (by simp [hk])

/-- psum reads its function only where the coordinates summed are bits. -/
theorem psum_congr_cube (z : ℕ → K) (G A : (ℕ → K) → K) (m : ℕ)
    (h : ∀ y, (∀ k, k < m → Bit (y k)) → G y = A y) :
    ∀ (L : List ℕ) (x : ℕ → K), (∀ k, k < m → k ∉ L → Bit (x k)) → psum z G L x = psum z A L x
  | [], x, hx => h x fun k hk => hx k hk (by simp)
  | i :: L, x, hx => by
    have step : ∀ c : K, Bit c → ∀ k, k < m → k ∉ L → Bit (Function.update x i c k) := by
      intro c hc k hk hkL
      rw [Function.update_apply]
      by_cases hki : k = i
      · rw [if_pos hki]
        exact hc
      · rw [if_neg hki]
        exact hx k hk (by simp [hki, hkL])
    show (1 - z i) * psum z G L (Function.update x i 0) + z i * psum z G L (Function.update x i 1) =
      (1 - z i) * psum z A L (Function.update x i 0) + z i * psum z A L (Function.update x i 1)
    rw [psum_congr_cube z G A m h L _ (step 0 (Or.inl rfl)),
      psum_congr_cube z G A m h L _ (step 1 (Or.inr rfl))]

/-- The point x with z's coordinates at the places L. -/
def placeZ (z : ℕ → K) : List ℕ → (ℕ → K) → ℕ → K
  | [], x => x
  | i :: L, x => Function.update (placeZ z L x) i (z i)

theorem placeZ_update (z : ℕ → K) {i : ℕ} (c : K) : ∀ (L : List ℕ) (x : ℕ → K), i ∉ L →
    placeZ z L (Function.update x i c) = Function.update (placeZ z L x) i c
  | [], _, _ => rfl
  | j :: L, x, h => by
    have hij : i ≠ j := fun e => h (by simp [e])
    have hL : i ∉ L := fun e => h (by simp [e])
    show Function.update (placeZ z L (Function.update x i c)) j (z j) =
      Function.update (Function.update (placeZ z L x) j (z j)) i c
    rw [placeZ_update z c L x hL, Function.update_comm hij]

theorem placeZ_mem (z : ℕ → K) {k : ℕ} : ∀ (L : List ℕ) (x : ℕ → K), k ∈ L → placeZ z L x k = z k
  | [], _, h => by simp at h
  | j :: L, x, h => by
    show Function.update (placeZ z L x) j (z j) k = z k
    rw [Function.update_apply]
    by_cases hkj : k = j
    · rw [if_pos hkj, hkj]
    · rw [if_neg hkj]
      exact placeZ_mem z L x ((List.mem_cons.mp h).resolve_left hkj)

theorem placeZ_not_mem (z : ℕ → K) {k : ℕ} : ∀ (L : List ℕ) (x : ℕ → K), k ∉ L →
    placeZ z L x k = x k
  | [], _, _ => rfl
  | j :: L, x, h => by
    have hkj : k ≠ j := fun e => h (by simp [e])
    have hL : k ∉ L := fun e => h (by simp [e])
    show Function.update (placeZ z L x) j (z j) k = x k
    rw [Function.update_apply, if_neg hkj]
    exact placeZ_not_mem z L x hL

/-- Of a map that is affine in each coordinate, psum is the value at z's coordinates. -/
theorem psum_affine {m : ℕ} (z : ℕ → K) {A : (ℕ → K) → K} (hA : AffIn m A) :
    ∀ (L : List ℕ) (x : ℕ → K), L.Nodup → (∀ i ∈ L, i < m) → psum z A L x = A (placeZ z L x)
  | [], _, _, _ => rfl
  | i :: L, x, hn, hm => by
    have hiL : i ∉ L := (List.nodup_cons.mp hn).1
    have hL : L.Nodup := (List.nodup_cons.mp hn).2
    have hm' : ∀ k ∈ L, k < m := fun k hk => hm k (by simp [hk])
    obtain ⟨a, b, e⟩ := hA (placeZ z L x) i (hm i (by simp))
    show (1 - z i) * psum z A L (Function.update x i 0) + z i * psum z A L (Function.update x i 1) =
      A (Function.update (placeZ z L x) i (z i))
    rw [psum_affine z hA L _ hL hm', psum_affine z hA L _ hL hm', placeZ_update z 0 L x hiL,
      placeZ_update z 1 L x hiL, e 0, e 1, e (z i)]
    ring

/-- **WHAT A LEVEL OWES TO THE MASKED SUMCHECK's LAW.** L: the coordinates in the order of the
rounds:
each of the m coordinates just once. x0: the point in which the challenges are laid; behind the m
coordinates it is z. wt i: the variable of coordinate i, wY: the further variable, as whichever
records
the text has: each with three coefficients, summed with the equality weights at z i, and at 0. -/
theorem isSum_level {m : ℕ} {A B : (ℕ → K) → K} (h : Step m A B) (mL mR : K) (z x0 : ℕ → K)
    (wt : ℕ → Wt K) (wY : Wt K) (hw : ∀ i, SumsAt (wt i) (z i)) (hwY : SumsAt wY 0)
    (L : List ℕ) (hn : L.Nodup) (hlt : ∀ i ∈ L, i < m) (hall : ∀ k, k < m → k ∈ L)
    (hx : ∀ k, m ≤ k → x0 k = z k) :
    IsSum (L.map wt ++ [wY]) (summand (lvY B mL mR) L x0) (A z) := by
  have hY : ∀ x, ∃ q : K[X], q.natDegree < 3 ∧ ∀ y, q.eval y = lvY B mL mR x y := fun x => by
    obtain ⟨q, hd, hq⟩ := two_lines (B (pcons 0 x)) mL (B (pcons 1 x)) mR
    exact ⟨q, hd, fun y => by
      rw [hq]
      unfold lvY
      ring⟩
  have hG : QuadIn m fun x => lvY B mL mR x 0 := fun x i hi => by
    obtain ⟨a0, b0, e0⟩ := h.affB (pcons 0 x) (i + 1) (by omega)
    obtain ⟨a1, b1, e1⟩ := h.affB (pcons 1 x) (i + 1) (by omega)
    obtain ⟨q, hd, hq⟩ := two_lines a0 b0 a1 b1
    exact ⟨q, hd, fun c => by
      rw [hq]
      show _ = lvY B mL mR (Function.update x i c) 0
      unfold lvY
      rw [pcons_update, pcons_update, e0, e1]
      ring⟩
  have h1 := isSum_summand z wt wY hw hwY (lvY B mL mR) hY hG L x0 hn hlt
  have h2 : psum z (fun x => lvY B mL mR x 0) L x0 = A z := by
    rw [psum_congr_cube z _ A m (fun y hy => by
        show lvY B mL mR y 0 = A y
        rw [h.prod y hy]
        unfold lvY
        ring) L x0 (fun k hk hkL => absurd (hall k hk) hkL),
      psum_affine z h.affA L x0 hn hlt]
    congr 1
    funext k
    by_cases hk : k ∈ L
    · exact placeZ_mem z L x0 hk
    · rw [placeZ_not_mem z L x0 hk]
      exact hx k (by
        by_contra hc
        exact hk (hall k (by omega)))
  rw [h2] at h1
  exact h1

end OnBytes.Desc.First.P2
