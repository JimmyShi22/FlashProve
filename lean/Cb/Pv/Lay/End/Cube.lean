-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Cube.lean: the multilinear extension of a vector whose index has three parts.

Lemmas on Blocks.ext and Blocks.eqN alone; no function of a verifier stands in a statement. An
index of a + (b + c) bits is read as (x | y | p): x the top a bits, y the next b, p the last c.

Main theorems.
 - ext_three: the extension as a sum over x and y of equality weights times an extension over p.
 - eqN_half: at coordinates that all equal h, with 1 - h = h, every equality weight is a power of h.
 - ext_plain: so, at such coordinates in the middle part, the extension is that power times the
   extension over (x | p) of the plain sum over y.
 - ext_half: the same for an index of two parts (y | p).
 - cube_squares: ext_plain for the square of a vector that is 0 outside x < n, y < d.
 - cube_point: the extension of a vector that is 0 outside x < n, y < B 2^s and a combination of nl
   vectors inside, as one sum over (x | block of y | number of the vector), block by block.


-/
import Blocks.LookupCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End

open Finset
open Blocks (ext eqN)

variable {K : Type} [Field K]

/-- A sum of a function that is 0 from n on. -/
theorem sum_pad {n N : ℕ} (h : n ≤ N) (f : ℕ → K) :
    ∑ x ∈ range N, (if x < n then f x else 0) = ∑ x ∈ range n, f x := by
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_filter, mem_range]
  omega

/-- Quotient and remainder of q m + l for l below m. -/
theorem div_mod_at (q l m : ℕ) (h : l < m) : (q * m + l) / m = q ∧ (q * m + l) % m = l := by
  have hm : 0 < m := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt h, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

/-- The three parts of the index (x | y | p). -/
theorem idx_three (b c x y p : ℕ) (hy : y < 2 ^ b) (hp : p < 2 ^ c) :
    (x * 2 ^ (b + c) + (y * 2 ^ c + p)) / 2 ^ (b + c) = x ∧
      (x * 2 ^ (b + c) + (y * 2 ^ c + p)) / 2 ^ c % 2 ^ b = y ∧
      (x * 2 ^ (b + c) + (y * 2 ^ c + p)) % 2 ^ c = p := by
  have hlt : y * 2 ^ c + p < 2 ^ (b + c) := by
    have h1 : (y + 1) * 2 ^ c ≤ 2 ^ b * 2 ^ c := Nat.mul_le_mul_right _ hy
    rw [pow_add]
    have h2 : (y + 1) * 2 ^ c = y * 2 ^ c + 2 ^ c := by ring
    omega
  have e : x * 2 ^ (b + c) + (y * 2 ^ c + p) = (x * 2 ^ b + y) * 2 ^ c + p := by
    rw [pow_add]
    ring
  refine ⟨(div_mod_at x _ _ hlt).1, ?_, ?_⟩
  · rw [e, (div_mod_at (x * 2 ^ b + y) p _ hp).1, (div_mod_at x y _ hy).2]
  · rw [e, (div_mod_at (x * 2 ^ b + y) p _ hp).2]

/-- A sum over the indices (y | p). -/
theorem sum_two (b c : ℕ) (g : ℕ → K) :
    ∑ θ ∈ range (2 ^ (b + c)), g θ =
      ∑ y ∈ range (2 ^ b), ∑ p ∈ range (2 ^ c), g (y * 2 ^ c + p) := by
  rw [pow_add 2 b c, Alg.sum_range_mul_add]

/-- The equality weight from an offset on is that of the shifted point. -/
theorem eqN_off (m off : ℕ) (z : ℕ → K) (x : ℕ) :
    eqN m off z x = eqN m 0 (fun j => z (off + j)) x := by
  unfold Blocks.eqN
  exact prod_congr rfl fun t _ => by rw [Nat.zero_add]

/-- The extension of a vector on the indices (x | y | p). -/
theorem ext_three (a b c : ℕ) (f : ℕ → ℕ → ℕ → K) (z : ℕ → K) :
    ext (a + (b + c)) (fun X => f (X / 2 ^ (b + c)) (X / 2 ^ c % 2 ^ b) (X % 2 ^ c)) z =
      ∑ x ∈ range (2 ^ a), eqN a 0 z x * ∑ y ∈ range (2 ^ b), eqN b a z y *
        ext c (fun p => f x y p) (fun j => z (a + b + j)) := by
  rw [Blocks.ext_two]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_two, mul_sum]
  refine sum_congr rfl fun y hy => ?_
  unfold Blocks.ext
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3⟩ := idx_three b c x y p (mem_range.mp hy) (mem_range.mp hp)
  beta_reduce
  rw [h1, h2, h3, Blocks.eqN_append' b c a z y (mem_range.mp hp), eqN_off c (a + b) z p]
  ring

/-- At coordinates that all equal h, with 1 - h = h, every equality weight is h^m. -/
theorem eqN_half (m off : ℕ) (z : ℕ → K) (h : K) (hh : 1 - h = h)
    (hz : ∀ t, t < m → z (off + t) = h) (x : ℕ) : eqN m off z x = h ^ m := by
  unfold Blocks.eqN
  have e : ∀ t ∈ range m,
      (if x.testBit (m - 1 - t) then z (off + t) else 1 - z (off + t)) = h := fun t ht => by
    rw [hz t (mem_range.mp ht), hh, ite_self]
  rw [prod_congr rfl e, prod_const, card_range]

/-- With such coordinates in the middle part, the extension is h^b times the extension over
(x | p) of the plain sum over y. -/
theorem ext_plain (a b c : ℕ) (f : ℕ → ℕ → ℕ → K) (z : ℕ → K) (h : K) (hh : 1 - h = h)
    (hz : ∀ t, t < b → z (a + t) = h) :
    ext (a + (b + c)) (fun X => f (X / 2 ^ (b + c)) (X / 2 ^ c % 2 ^ b) (X % 2 ^ c)) z =
      h ^ b * ∑ x ∈ range (2 ^ a), eqN a 0 z x *
        ext c (fun p => ∑ y ∈ range (2 ^ b), f x y p) (fun j => z (a + b + j)) := by
  rw [ext_three, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [Blocks.ext_sum]
  have e : ∑ y ∈ range (2 ^ b), eqN b a z y * ext c (fun p => f x y p) (fun j => z (a + b + j)) =
      h ^ b * ∑ y ∈ range (2 ^ b), ext c (fun p => f x y p) (fun j => z (a + b + j)) := by
    rw [mul_sum]
    exact sum_congr rfl fun y _ => by rw [eqN_half b a z h hh hz y]
  rw [e]
  ring

/-- The same without a first part: at a point whose first b coordinates all equal h, the extension
is h^b times the extension over p of the plain sum over y. -/
theorem ext_half (b c : ℕ) (v : ℕ → K) (z : ℕ → K) (h : K) (hh : 1 - h = h)
    (hz : ∀ t, t < b → z t = h) :
    ext (b + c) v z =
      h ^ b * ext c (fun p => ∑ y ∈ range (2 ^ b), v (y * 2 ^ c + p)) (fun j => z (b + j)) := by
  rw [Blocks.ext_two, Blocks.ext_sum, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  unfold Blocks.ext
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [eqN_half b 0 z h hh (fun t ht => by rw [Nat.zero_add]; exact hz t ht) y, eqN_off c b z p]
  ring

/-- ext_plain for the square of a vector that is q inside x < n, y < d and 0 outside. -/
theorem cube_squares (a b c n d : ℕ) (hn : n ≤ 2 ^ a) (hd : d ≤ 2 ^ b) (q : ℕ → ℕ → ℕ → K)
    (z : ℕ → K) (h : K) (hh : 1 - h = h) (hz : ∀ t, t < b → z (a + t) = h) :
    ext (a + (b + c))
        (fun X => (if X / 2 ^ (b + c) < n ∧ X / 2 ^ c % 2 ^ b < d then
          q (X / 2 ^ (b + c)) (X / 2 ^ c % 2 ^ b) (X % 2 ^ c) else 0) ^ 2) z =
      h ^ b * ∑ ν ∈ range n, eqN a 0 z ν *
        ext c (fun p => ∑ j ∈ range d, q ν j p ^ 2) (fun j => z (a + b + j)) := by
  have inner : ∀ x p, ∑ y ∈ range (2 ^ b), (if x < n ∧ y < d then q x y p else 0) ^ 2 =
      if x < n then ∑ j ∈ range d, q x j p ^ 2 else 0 := by
    intro x p
    by_cases hx : x < n
    · rw [if_pos hx, ← sum_pad hd]
      refine sum_congr rfl fun y _ => ?_
      by_cases hy : y < d
      · rw [if_pos ⟨hx, hy⟩, if_pos hy]
      · rw [if_neg (fun k => hy k.2), if_neg hy]
        ring
    · rw [if_neg hx]
      exact sum_eq_zero fun y _ => by
        rw [if_neg (fun k => hx k.1)]
        ring
  refine (ext_plain a b c (fun x y p => (if x < n ∧ y < d then q x y p else 0) ^ 2) z h hh
    hz).trans ?_
  congr 1
  rw [← sum_pad hn]
  refine sum_congr rfl fun x _ => ?_
  simp only [inner]
  by_cases hx : x < n
  · simp only [if_pos hx]
  · simp only [if_neg hx]
    rw [Blocks.ext_zero_of_forall (fun _ _ => rfl), mul_zero]

/-- The extension of a vector that is, inside x < n and y < B 2^s, the combination under gl of the
nl vectors bb x l, and 0 outside: as one sum over i = (x | block kh of y | l), block by block. -/
theorem cube_point (a b s c n B nl : ℕ) (hn : n ≤ 2 ^ a) (hB : B ≤ 2 ^ b) (gl : ℕ → K)
    (bb : ℕ → ℕ → ℕ → ℕ → K) (z : ℕ → K) :
    ext (a + ((b + s) + c))
        (fun X => if X / 2 ^ ((b + s) + c) < n ∧ X / 2 ^ c % 2 ^ (b + s) < B * 2 ^ s then
          ∑ l ∈ range nl, gl l *
            bb (X / 2 ^ ((b + s) + c)) l (X / 2 ^ c % 2 ^ (b + s)) (X % 2 ^ c) else 0) z =
      ∑ i ∈ range (n * B * nl),
        eqN (a + b) 0 z (i / nl / B * 2 ^ b + i / nl % B) * gl (i % nl) *
          ∑ r ∈ range (2 ^ s), eqN s (a + b) z r *
            ext c (fun p => bb (i / nl / B) (i % nl) (i / nl % B * 2 ^ s + r) p)
              (fun j => z (a + (b + s) + j)) := by
  -- the right side, over (x | kh | l)
  have hR : ∑ i ∈ range (n * B * nl),
        eqN (a + b) 0 z (i / nl / B * 2 ^ b + i / nl % B) * gl (i % nl) *
          ∑ r ∈ range (2 ^ s), eqN s (a + b) z r *
            ext c (fun p => bb (i / nl / B) (i % nl) (i / nl % B * 2 ^ s + r) p)
              (fun j => z (a + (b + s) + j)) =
      ∑ x ∈ range n, ∑ kh ∈ range B, ∑ l ∈ range nl,
        eqN (a + b) 0 z (x * 2 ^ b + kh) * gl l *
          ∑ r ∈ range (2 ^ s), eqN s (a + b) z r *
            ext c (fun p => bb x l (kh * 2 ^ s + r) p) (fun j => z (a + (b + s) + j)) := by
    rw [Alg.sum_range_mul_add, Alg.sum_range_mul_add]
    refine sum_congr rfl fun x _ => sum_congr rfl fun kh hkh => sum_congr rfl fun l hl => ?_
    rw [(div_mod_at (x * B + kh) l nl (mem_range.mp hl)).1,
      (div_mod_at (x * B + kh) l nl (mem_range.mp hl)).2,
      (div_mod_at x kh B (mem_range.mp hkh)).1, (div_mod_at x kh B (mem_range.mp hkh)).2]
  rw [hR]
  refine (ext_three a (b + s) c (fun x y p => if x < n ∧ y < B * 2 ^ s then
    ∑ l ∈ range nl, gl l * bb x l y p else 0) z).trans ?_
  beta_reduce
  rw [← sum_pad hn]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x < n
  · rw [if_pos hx, sum_two, mul_sum, ← sum_pad hB]
    refine sum_congr rfl fun kh hkh => ?_
    by_cases hk : kh < B
    · rw [if_pos hk]
      have hin : ∀ r ∈ range (2 ^ s),
          ext c (fun p => if x < n ∧ kh * 2 ^ s + r < B * 2 ^ s then
            ∑ l ∈ range nl, gl l * bb x l (kh * 2 ^ s + r) p else 0)
            (fun j => z (a + (b + s) + j)) =
          ∑ l ∈ range nl, gl l *
            ext c (fun p => bb x l (kh * 2 ^ s + r) p) (fun j => z (a + (b + s) + j)) := by
        intro r hr
        have hy : kh * 2 ^ s + r < B * 2 ^ s := by
          have h1 : (kh + 1) * 2 ^ s ≤ B * 2 ^ s := Nat.mul_le_mul_right _ hk
          have h2 : (kh + 1) * 2 ^ s = kh * 2 ^ s + 2 ^ s := by ring
          have h3 := mem_range.mp hr
          omega
        simp only [if_pos (And.intro hx hy)]
        rw [Blocks.ext_sum]
        exact sum_congr rfl fun l _ => Blocks.ext_smul _ _ _ _
      calc eqN a 0 z x * ∑ r ∈ range (2 ^ s), eqN (b + s) a z (kh * 2 ^ s + r) *
            ext c (fun p => if x < n ∧ kh * 2 ^ s + r < B * 2 ^ s then
              ∑ l ∈ range nl, gl l * bb x l (kh * 2 ^ s + r) p else 0)
              (fun j => z (a + (b + s) + j))
          = ∑ r ∈ range (2 ^ s), ∑ l ∈ range nl,
              eqN a 0 z x * (eqN (b + s) a z (kh * 2 ^ s + r) * (gl l *
                ext c (fun p => bb x l (kh * 2 ^ s + r) p) (fun j => z (a + (b + s) + j)))) := by
            rw [mul_sum]
            refine sum_congr rfl fun r hr => ?_
            rw [hin r hr, mul_sum, mul_sum]
        _ = ∑ l ∈ range nl, ∑ r ∈ range (2 ^ s),
              eqN a 0 z x * (eqN (b + s) a z (kh * 2 ^ s + r) * (gl l *
                ext c (fun p => bb x l (kh * 2 ^ s + r) p) (fun j => z (a + (b + s) + j)))) :=
            sum_comm
        _ = _ := by
            refine sum_congr rfl fun l _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun r hr => ?_
            rw [Blocks.eqN_append' b s a z kh (mem_range.mp hr),
              Blocks.eqN_append' a b 0 z x (mem_range.mp hkh), Nat.zero_add]
            ring
    · rw [if_neg hk, mul_sum]
      refine sum_eq_zero fun r _ => ?_
      have hy : ¬ kh * 2 ^ s + r < B * 2 ^ s := by
        have h1 : B * 2 ^ s ≤ kh * 2 ^ s := Nat.mul_le_mul_right _ (Nat.le_of_not_lt hk)
        omega
      simp only [if_neg (fun k : x < n ∧ kh * 2 ^ s + r < B * 2 ^ s => hy k.2)]
      rw [Blocks.ext_zero_of_forall (fun _ _ => rfl), mul_zero, mul_zero]
  · rw [if_neg hx]
    have hz : ∀ y p, (if x < n ∧ y < B * 2 ^ s then
        ∑ l ∈ range nl, gl l * bb x l y p else 0) = 0 := fun y p => if_neg fun k => hx k.1
    simp only [hz]
    refine mul_eq_zero_of_right _ (sum_eq_zero fun y _ => ?_)
    rw [Blocks.ext_zero_of_forall (fun _ _ => rfl), mul_zero]

end Cb.Pv.Lay.End
