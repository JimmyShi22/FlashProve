-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SquaresPoint.lean: the sum in the third claim of group 2 of the layers' own rounds
is one extension at the product layer's own point.

Johnson/Road/K4/Says.lean (`norms_says`) gives the squares' end value as a sum over the norms, the
blocks of features and the limbs, under the verifier's weights. Here that sum is shown to be the
multilinear extension, at the whole point r of the product layer, of one vector on the indices
(norm | feature | position): the limbs of the stream batched under the powers gp, and 0 at a padded
norm or feature.

  `sqV`: the vector.
  `squares_point`: the sum is ext (..) sqV (pt r).

Limits. An identity of sums: no draw, no soundness.
-/
import Johnson.Road.Rows.GatedEndsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open Blocks (ext eqN)
open OnBytes.Road.Rows (ext_blocks cut_two)

variable {K : Type} [Field K]

theorem cut_gen (n Y i : ℕ) (hi : i < n) : (Y * n + i) / n = Y ∧ (Y * n + i) % n = i := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- A sum whose terms from n on are 0. -/
theorem sum_range_le {n m : ℕ} (h : n ≤ m) (f : ℕ → K) (hz : ∀ i, n ≤ i → i < m → f i = 0) :
    ∑ i ∈ range m, f i = ∑ i ∈ range n, f i :=
  (Finset.sum_subset (Finset.range_mono h) fun i hi hni =>
    hz i (by simpa using hni) (mem_range.mp hi)).symm

/-- (k | s) is below (B | 0) exactly if k is below B. -/
theorem block_lt (a k s B : ℕ) (hs : s < a) : k * a + s < B * a ↔ k < B := by
  constructor
  · intro h
    by_contra hk
    have h1 : B * a ≤ k * a := Nat.mul_le_mul_right a (Nat.le_of_not_lt hk)
    omega
  · intro h
    have h1 : (k + 1) * a ≤ B * a := Nat.mul_le_mul_right a h
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega

/-- The limbs b of norm ν, feature j, position p, batched under gp; 0 at a norm from NI on and at a
feature from d on. The index is (ν | j | p), with lPd bits for j and lT for p. -/
def sqV (NI d lPd nl lT : ℕ) (gp : ℕ → K) (b : ℕ → ℕ → ℕ → ℕ → K) (X : ℕ) : K :=
  if X / 2 ^ lT / 2 ^ lPd < NI ∧ X / 2 ^ lT % 2 ^ lPd < d then
    ∑ l ∈ range nl, gp l * b (X / 2 ^ lT / 2 ^ lPd) l (X / 2 ^ lT % 2 ^ lPd) (X % 2 ^ lT)
  else 0

theorem sqV_at {NI B lPd ls nl lT : ℕ} (hls : ls ≤ lPd) (gp : ℕ → K) (b : ℕ → ℕ → ℕ → ℕ → K)
    {ν kh s i : ℕ} (hkh : kh < 2 ^ (lPd - ls)) (hs : s < 2 ^ ls) (hi : i < 2 ^ lT) :
    sqV NI (B * 2 ^ ls) lPd nl lT gp b (((ν * 2 ^ (lPd - ls) + kh) * 2 ^ ls + s) * 2 ^ lT + i) =
      if ν < NI ∧ kh < B then ∑ l ∈ range nl, gp l * b ν l (kh * 2 ^ ls + s) i else 0 := by
  have hP : 2 ^ lPd = 2 ^ (lPd - ls) * 2 ^ ls := by
    rw [← pow_add]
    congr 1
    omega
  obtain ⟨d1, d2⟩ := cut_two lT ((ν * 2 ^ (lPd - ls) + kh) * 2 ^ ls + s) i hi
  have hY : (ν * 2 ^ (lPd - ls) + kh) * 2 ^ ls + s = ν * 2 ^ lPd + (kh * 2 ^ ls + s) := by
    rw [hP]
    ring
  have hlt : kh * 2 ^ ls + s < 2 ^ lPd := by
    rw [hP]
    exact (block_lt (2 ^ ls) kh s _ hs).mpr hkh
  obtain ⟨c1, c2⟩ := cut_gen (2 ^ lPd) ν (kh * 2 ^ ls + s) hlt
  unfold sqV
  rw [d1, d2, hY, c1, c2]
  simp only [block_lt (2 ^ ls) kh s B hs]

/-- The sum of the third claim of group 2 is one extension at the product layer's point r. -/
theorem squares_point (ρ : Reading K) {r e : Array E} {la lNI lPd ls lT NI B nl : ℕ}
    (hls : ls ≤ lPd) (he : hiTab r la (lNI + lPd - ls) = .ok e) (hNI : NI ≤ 2 ^ lNI)
    (hB : B ≤ 2 ^ (lPd - ls)) (gp : ℕ → K) (b : ℕ → ℕ → ℕ → ℕ → K) :
    (∑ x ∈ range (NI * B * nl),
      ρ.val (e.getD (x / nl / B * 2 ^ lPd / 2 ^ ls + x / nl % B) zeroE) * gp (x % nl) *
        ∑ s ∈ range (2 ^ ls), eqN ls 0 (fun j => pt ρ r (lNI + lPd - ls + j)) s *
          ext lT (fun p => b (x / nl / B) (x % nl) (x / nl % B * 2 ^ ls + s) p)
            (fun j => pt ρ r (lNI + lPd - ls + ls + j))) =
      ext (lNI + lPd - ls + ls + lT) (sqV NI (B * 2 ^ ls) lPd nl lT gp b) (pt ρ r) := by
  have hg : 2 ^ (lNI + lPd - ls) = 2 ^ lNI * 2 ^ (lPd - ls) := by
    rw [← pow_add]
    congr 1
    omega
  have hP : 2 ^ lPd = 2 ^ (lPd - ls) * 2 ^ ls := by
    rw [← pow_add]
    congr 1
    omega
  rw [ext_blocks, hg, Alg.sum_range_mul_add (2 ^ lNI) (2 ^ (lPd - ls)),
    Alg.sum_range_mul_add (NI * B) nl, Alg.sum_range_mul_add NI B]
  -- what one block (ν, kh) gives on the right
  have key : ∀ ν kh, ν < 2 ^ lNI → kh < 2 ^ (lPd - ls) →
      (∑ s ∈ range (2 ^ ls),
        eqN (lNI + lPd - ls + ls) 0 (pt ρ r) ((ν * 2 ^ (lPd - ls) + kh) * 2 ^ ls + s) *
          ext lT (fun i => sqV NI (B * 2 ^ ls) lPd nl lT gp b
            (((ν * 2 ^ (lPd - ls) + kh) * 2 ^ ls + s) * 2 ^ lT + i))
            (fun j => pt ρ r (lNI + lPd - ls + ls + j))) =
        if ν < NI ∧ kh < B then
          ∑ l ∈ range nl, ρ.val (e.getD (ν * 2 ^ (lPd - ls) + kh) zeroE) * gp l *
            ∑ s ∈ range (2 ^ ls), eqN ls 0 (fun j => pt ρ r (lNI + lPd - ls + j)) s *
              ext lT (fun p => b ν l (kh * 2 ^ ls + s) p)
                (fun j => pt ρ r (lNI + lPd - ls + ls + j))
        else 0 := by
    intro ν kh hν hkh
    have hk : ν * 2 ^ (lPd - ls) + kh < 2 ^ (lNI + lPd - ls) := by
      rw [hg]
      exact (block_lt (2 ^ (lPd - ls)) ν kh _ hkh).mpr hν
    by_cases hc : ν < NI ∧ kh < B
    · rw [if_pos hc]
      simp_rw [mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun s hs => ?_
      have hs' := mem_range.mp hs
      rw [Hd.squares_weight ρ he (low := fun j => pt ρ r (lNI + lPd - ls + j)) (fun j _ => rfl)
        hk hs']
      have e1 : ext lT (fun i => sqV NI (B * 2 ^ ls) lPd nl lT gp b
          (((ν * 2 ^ (lPd - ls) + kh) * 2 ^ ls + s) * 2 ^ lT + i))
          (fun j => pt ρ r (lNI + lPd - ls + ls + j)) =
          ∑ l ∈ range nl, gp l * ext lT (fun p => b ν l (kh * 2 ^ ls + s) p)
            (fun j => pt ρ r (lNI + lPd - ls + ls + j)) := by
        rw [Blocks.ext_congr (w := fun i => ∑ l ∈ range nl, gp l * b ν l (kh * 2 ^ ls + s) i)
          (fun i hi => by rw [sqV_at hls gp b hkh hs' hi, if_pos hc])]
        rw [Blocks.ext_sum]
        exact sum_congr rfl fun l _ => Blocks.ext_smul _ _ _ _
      rw [e1, mul_sum]
      refine sum_congr rfl fun l _ => ?_
      ring
    · rw [if_neg hc]
      refine sum_eq_zero fun s hs => ?_
      rw [Blocks.ext_zero_of_forall (fun i hi => by
        rw [sqV_at hls gp b hkh (mem_range.mp hs) hi, if_neg hc]), mul_zero]
  rw [sum_congr rfl fun ν hν => sum_congr rfl fun kh hkh =>
    key ν kh (mem_range.mp hν) (mem_range.mp hkh)]
  rw [sum_range_le hNI _ (fun ν h1 _ => sum_eq_zero fun kh _ => by
    rw [if_neg (fun h => by omega)])]
  refine sum_congr rfl fun ν hν => ?_
  rw [sum_range_le hB _ (fun kh h1 _ => by rw [if_neg (fun h => by omega)])]
  refine sum_congr rfl fun kh hkh => ?_
  rw [if_pos ⟨mem_range.mp hν, mem_range.mp hkh⟩]
  refine sum_congr rfl fun l hl => ?_
  obtain ⟨a1, a2⟩ := cut_gen nl (ν * B + kh) l (mem_range.mp hl)
  obtain ⟨b1, b2⟩ := cut_gen B ν kh (mem_range.mp hkh)
  have hdiv : ν * 2 ^ lPd / 2 ^ ls = ν * 2 ^ (lPd - ls) := by
    rw [hP, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos ls)]
  rw [a1, a2, b1, b2, hdiv]

#print axioms squares_point

end OnBytes.Road.K4
