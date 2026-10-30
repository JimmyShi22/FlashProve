-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Ends/Pieces.lean: the multilinear extension of a vector that is laid in pieces, over
any field E, in the library's Blocks.ext.

Definitions, statements and proofs.
Main names:
  `blockFn off b f`: f on the block of 2^b places from off on, 0 elsewhere.
  `pwVec off b key pad ps`: a vector laid in pieces. A piece p holds the place X if
    off p ≤ X < off p + 2^(b p). The first piece p of the list ps that holds X gives the entry
    key p (X - off p); where no piece holds X, the entry is the padding value pad.
  `wpAt n off b pt`: a piece's weight, the equality weight of off / 2^b at the first n - b
    coordinates of pt. `innAt n b pt`: the inner point, the last b of the n coordinates.
  `ext_rows`: without a premise, the extension over k1 + k2 coordinates, by 2^k1 rows.
  `ext_block`: under b ≤ n, 2^b ∣ off and off + 2^b ≤ 2^n:
      ext n (blockFn off b f) pt = wpAt n off b pt * ext b f (innAt n b pt).
  `ext_pwVec`: if every piece p of ps is aligned and inside (b p ≤ n, 2^(b p) ∣ off p,
    off p + 2^(b p) ≤ 2^n) and the pieces are pairwise apart:
      ext n (pwVec off b key pad ps) pt
        = the sum over the pieces of wpAt * ext (b p) (key p) (the inner point)
          + pad * (1 - the sum of the pieces' weights).
  `pwVec_find`: without a premise, the vector written with List.find? is pwVec.
Limits: algebra alone. The file says nothing on which vector of the protocol is laid so, and nothing
on a claim, a round or a message.

-/
import Blocks.Ext
import Blocks.EqN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open Finset

variable {E : Type} [Field E]

/-- A sum over N n arguments, by n blocks of N. -/
theorem sum_blocks {K : Type} [AddCommMonoid K] (f : ℕ → K) (N n : ℕ) :
    ∑ i ∈ range (N * n), f i = ∑ i ∈ range n, ∑ c ∈ range N, f (N * i + c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- eqN from an offset on is eqN of the shifted point. -/
theorem eqN_shift (m off : ℕ) (a : ℕ → E) (z : ℕ) :
    Blocks.eqN m off a z = Blocks.eqN m 0 (fun t => a (off + t)) z := by
  unfold Blocks.eqN
  simp only [Nat.zero_add]

/-- **The extension by rows.** -/
theorem ext_rows (k1 k2 : ℕ) (v pt : ℕ → E) :
    Blocks.ext (k1 + k2) v pt = ∑ i ∈ range (2 ^ k1), Blocks.eqN k1 0 pt i *
      Blocks.ext k2 (fun c => v (2 ^ k2 * i + c)) (fun t => pt (k1 + t)) := by
  unfold Blocks.ext
  rw [show 2 ^ (k1 + k2) = 2 ^ k2 * 2 ^ k1 by rw [pow_add, Nat.mul_comm], sum_blocks]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [Blocks.eqN_split k1 k2 pt i (mem_range.1 hc), mul_assoc, eqN_shift k2 k1]

/-- f on the block of 2^b places from off on, 0 elsewhere. -/
def blockFn (off b : ℕ) (f : ℕ → E) (X : ℕ) : E :=
  if off ≤ X ∧ X < off + 2 ^ b then f (X - off) else 0

/-- The extension of a block's vector, with the numbers written as m + b and 2^b * k. -/
theorem ext_block' (m b k : ℕ) (hk : k < 2 ^ m) (f pt : ℕ → E) :
    Blocks.ext (m + b) (blockFn (2 ^ b * k) b f) pt =
      Blocks.eqN m 0 pt k * Blocks.ext b f (fun t => pt (m + t)) := by
  rw [ext_rows m b, sum_eq_single k]
  · congr 1
    apply Blocks.ext_congr
    intro c hc
    unfold blockFn
    rw [if_pos ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hc _⟩, Nat.add_sub_cancel_left]
  · intro i _ hik
    rw [Blocks.ext_zero_of_forall, mul_zero]
    intro c hc
    unfold blockFn
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    rcases Nat.lt_trichotomy i k with h | h | h
    · exfalso
      have h3 : 2 ^ b * (i + 1) ≤ 2 ^ b * k := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h3
      omega
    · exact h
    · exfalso
      have h3 : 2 ^ b * (k + 1) ≤ 2 ^ b * i := Nat.mul_le_mul_left _ h
      rw [Nat.mul_succ] at h3
      omega
  · intro hk'
    exact absurd (mem_range.2 hk) hk'

/-- A piece's weight at the point pt of n coordinates. -/
def wpAt (n off b : ℕ) (pt : ℕ → E) : E := Blocks.eqN (n - b) 0 pt (off / 2 ^ b)

/-- The inner point: the last b of n coordinates. -/
def innAt (n b : ℕ) (pt : ℕ → E) : ℕ → E := fun t => pt (n - b + t)

/-- **The extension of a block's vector.** -/
theorem ext_block {n b off : ℕ} (hb : b ≤ n) (hd : 2 ^ b ∣ off) (hle : off + 2 ^ b ≤ 2 ^ n)
    (f pt : ℕ → E) :
    Blocks.ext n (blockFn off b f) pt = wpAt n off b pt * Blocks.ext b f (innAt n b pt) := by
  obtain ⟨k, rfl⟩ := hd
  obtain ⟨m, rfl⟩ : ∃ m, n = m + b := ⟨n - b, by omega⟩
  have hp : 0 < 2 ^ b := Nat.pos_of_ne_zero (by positivity)
  have hk : k < 2 ^ m := by
    rw [pow_add, Nat.mul_comm (2 ^ m)] at hle
    have h3 : 2 ^ b * (k + 1) ≤ 2 ^ b * 2 ^ m := by rw [Nat.mul_succ]; exact hle
    exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_left h3 hp)
  unfold wpAt innAt
  rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left k hp]
  exact ext_block' m b k hk f pt

section Pw

variable {ι : Type} (off b : ι → ℕ)

/-- A vector laid in pieces: the first piece of the list that holds X gives its key number
X - off; where no piece holds X, the padding value. -/
def pwVec (key : ι → ℕ → E) (pad : E) : List ι → ℕ → E
  | [], _ => pad
  | p :: ps, X =>
    if off p ≤ X ∧ X < off p + 2 ^ b p then key p (X - off p) else pwVec key pad ps X

/-- Outside all pieces the vector holds the padding value. -/
theorem pwVec_outside (key : ι → ℕ → E) (pad : E) (ps : List ι) (X : ℕ)
    (h : ∀ p ∈ ps, ¬(off p ≤ X ∧ X < off p + 2 ^ b p)) : pwVec off b key pad ps X = pad := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show (if off p ≤ X ∧ X < off p + 2 ^ b p then key p (X - off p)
      else pwVec off b key pad ps X) = pad
    rw [if_neg (h p (List.mem_cons_self ..))]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **The extension of a vector laid in pieces.** -/
theorem ext_pwVec (n : ℕ) (key : ι → ℕ → E) (pad : E) (pt : ℕ → E) (ps : List ι)
    (hA : ∀ p ∈ ps, b p ≤ n ∧ 2 ^ b p ∣ off p ∧ off p + 2 ^ b p ≤ 2 ^ n)
    (hD : ps.Pairwise fun p q => off p + 2 ^ b p ≤ off q ∨ off q + 2 ^ b q ≤ off p) :
    Blocks.ext n (pwVec off b key pad ps) pt =
      (ps.map fun p => wpAt n (off p) (b p) pt *
        Blocks.ext (b p) (key p) (innAt n (b p) pt)).sum +
      pad * (1 - (ps.map fun p => wpAt n (off p) (b p) pt).sum) := by
  induction ps with
  | nil =>
    have h0 : pwVec off b key pad ([] : List ι) = fun _ => pad := rfl
    rw [h0, Blocks.ext_const]
    simp
  | cons p ps ih =>
    obtain ⟨hp, hps⟩ := List.pairwise_cons.1 hD
    have hsplit : pwVec off b key pad (p :: ps) = fun X =>
        pwVec off b key pad ps X + blockFn (off p) (b p) (fun κ => key p κ - pad) X := by
      funext X
      show (if off p ≤ X ∧ X < off p + 2 ^ b p then key p (X - off p)
        else pwVec off b key pad ps X) = _
      unfold blockFn
      by_cases hX : off p ≤ X ∧ X < off p + 2 ^ b p
      · rw [if_pos hX, if_pos hX, pwVec_outside off b key pad ps X]
        · ring
        · intro q hq hXq
          rcases hp q hq with h | h <;> omega
      · rw [if_neg hX, if_neg hX, add_zero]
    obtain ⟨h1, h2, h3⟩ := hA p (List.mem_cons_self ..)
    rw [hsplit, Blocks.ext_add, ih (fun q hq => hA q (List.mem_cons_of_mem _ hq)) hps,
      ext_block h1 h2 h3, Blocks.ext_sub, Blocks.ext_const]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The vector written with List.find? is pwVec. -/
theorem pwVec_find (key : ι → ℕ → E) (pad : E) (ps : List ι) (X : ℕ) :
    (match ps.find? fun p => decide (off p ≤ X ∧ X < off p + 2 ^ b p) with
      | some p => key p (X - off p)
      | none => pad) = pwVec off b key pad ps X := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    show _ = (if off p ≤ X ∧ X < off p + 2 ^ b p then key p (X - off p)
      else pwVec off b key pad ps X)
    by_cases hX : off p ≤ X ∧ X < off p + 2 ^ b p
    · rw [if_pos hX, List.find?_cons_of_pos (by simpa using hX)]
    · rw [if_neg hX, List.find?_cons_of_neg (by simpa using hX)]
      exact ih

end Pw

end OnBytes.Ends

#print axioms OnBytes.Ends.ext_block
#print axioms OnBytes.Ends.ext_pwVec
#print axioms OnBytes.Ends.pwVec_find
