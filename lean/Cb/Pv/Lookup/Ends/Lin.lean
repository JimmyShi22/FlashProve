-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Ends/Lin.lean: rules for the multilinear extension (the library's Blocks.ext) of
vectors that are linear in other vectors, or that read only some bits of their index; over any field
E.

Statements and proofs; no definition. Each stands without a premise, but for unit_lin.
Main names:
  `ext_linL`: the extension of k + a list of multiples of vectors is k + the multiples of the
    vectors' extensions.
  `sum_linL`: a weighted sum, over a list, of terms k + a list of multiples.
  `unit_lin`: both together. If for every piece p of the list l the keys are
    key p κ = k + the sum over L of x.1 * x.2 p κ, then the weighted sum over l of the extensions of
    the keys is k times the sum of the weights, plus the multiples of the components' weighted sums.
  `ext_field`: the extension of a vector that reads one field of bits of its index (w bits, lo
    bits above the bottom, below a further bits) is the extension of the function of that field at
    the field's coordinates a, .., a + w - 1.
  `ext_dropLow`, `ext_dropHigh`: its two halves. A vector on a + lo index bits that reads the top a
    bits alone has the extension of the function of these bits at the coordinates 0, .., a - 1; a
    vector on a + w index bits that reads the low w bits alone, at the coordinates a, .., a + w - 1.
  `ext_allOnes`: the indicator of "all w bits are 1" has as extension the product of the
    coordinates.
  `ext_top`: the top bit splits the extension into a part with 1 - z 0 and a part with z 0.
  `sum_eqN`: the equality weights of a point sum to 1.
Limits: algebra alone. The file says nothing on which vector of the protocol has such a form.

-/
import Cb.Pv.Lookup.Ends.Pieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open Finset

variable {E : Type} [Field E]

/-- The extension of k + a list of multiples of vectors. -/
theorem ext_linL (b : ℕ) (z : ℕ → E) (k : E) (L : List (E × (ℕ → E))) :
    Blocks.ext b (fun κ => k + (L.map fun x => x.1 * x.2 κ).sum) z =
      k + (L.map fun x => x.1 * Blocks.ext b x.2 z).sum := by
  induction L with
  | nil =>
    have h0 : (fun κ : ℕ => k + (([] : List (E × (ℕ → E))).map fun x => x.1 * x.2 κ).sum) =
        fun _ => k := by
      funext κ
      simp
    rw [h0, Blocks.ext_const]
    simp
  | cons x L ih =>
    have h1 : (fun κ => k + ((x :: L).map fun y => y.1 * y.2 κ).sum) =
        fun κ => (k + (L.map fun y => y.1 * y.2 κ).sum) + x.1 * x.2 κ := by
      funext κ
      simp only [List.map_cons, List.sum_cons]
      ring
    have h2 : Blocks.ext b (fun κ => (k + (L.map fun y => y.1 * y.2 κ).sum) + x.1 * x.2 κ) z =
        Blocks.ext b (fun κ => k + (L.map fun y => y.1 * y.2 κ).sum) z +
          Blocks.ext b (fun κ => x.1 * x.2 κ) z := Blocks.ext_add b _ _ z
    rw [h1, h2, ih, Blocks.ext_smul]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- A weighted sum, over a list l, of k + a list of multiples. -/
theorem sum_linL {ι κ' : Type} (l : List ι) (w : ι → E) (k : E) (L : List κ') (c : κ' → E)
    (G : κ' → ι → E) :
    (l.map fun p => w p * (k + (L.map fun x => c x * G x p).sum)).sum =
      k * (l.map w).sum + (L.map fun x => c x * (l.map fun p => w p * G x p).sum).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil, add_zero]
    induction l with
    | nil => simp
    | cons p l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  | cons x L ih =>
    have h1 : (l.map fun p => w p * (k + ((x :: L).map fun y => c y * G y p).sum)).sum =
        (l.map fun p => w p * (k + (L.map fun y => c y * G y p).sum)).sum +
          c x * (l.map fun p => w p * G x p).sum := by
      clear ih
      induction l with
      | nil => simp
      | cons p l ihl =>
        simp only [List.map_cons, List.sum_cons] at ihl ⊢
        rw [ihl]
        ring
    rw [h1, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- **A unit's weighted sum of extensions, by components.** -/
theorem unit_lin {ι : Type} (l : List ι) (w : ι → E) (b : ι → ℕ) (z : ι → ℕ → E)
    (key : ι → ℕ → E) (k : E) (L : List (E × (ι → ℕ → E)))
    (hkey : ∀ p ∈ l, ∀ κ, key p κ = k + (L.map fun x => x.1 * x.2 p κ).sum) :
    (l.map fun p => w p * Blocks.ext (b p) (key p) (z p)).sum =
      k * (l.map w).sum +
        (L.map fun x => x.1 * (l.map fun p => w p * Blocks.ext (b p) (x.2 p) (z p)).sum).sum := by
  rw [← sum_linL l w k L (fun x => x.1) fun x p => Blocks.ext (b p) (x.2 p) (z p)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have h1 : key p = fun κ => k + ((L.map fun x => (x.1, x.2 p)).map fun y => y.1 * y.2 κ).sum := by
    funext κ
    rw [hkey p hp κ, List.map_map]
    rfl
  rw [h1, ext_linL, List.map_map]
  rfl

/-- The weights of a point sum to 1. -/
theorem sum_eqN (g : ℕ) (pt : ℕ → E) : ∑ X ∈ range (2 ^ g), Blocks.eqN g 0 pt X = 1 := by
  have h := Blocks.ext_const g (1 : E) pt
  unfold Blocks.ext at h
  simpa using h

/-- The extension of a vector that does not read its low lo bits. -/
theorem ext_dropLow (a lo : ℕ) (f z : ℕ → E) :
    Blocks.ext (a + lo) (fun κ => f (κ / 2 ^ lo)) z = Blocks.ext a f z := by
  rw [ext_rows a lo]
  unfold Blocks.ext
  refine sum_congr rfl fun i _ => ?_
  congr 1
  have hp : 0 < 2 ^ lo := Nat.pos_of_ne_zero (by positivity)
  have h1 : ∀ c ∈ range (2 ^ lo),
      Blocks.eqN lo 0 (fun t => z (a + t)) c * f ((2 ^ lo * i + c) / 2 ^ lo) =
      Blocks.eqN lo 0 (fun t => z (a + t)) c * f i := by
    intro c hc
    rw [Nat.mul_add_div hp, Nat.div_eq_of_lt (mem_range.1 hc), Nat.add_zero]
  rw [sum_congr rfl h1, ← sum_mul, sum_eqN, one_mul]

/-- The extension of a vector that reads its low w bits alone. -/
theorem ext_dropHigh (a w : ℕ) (f z : ℕ → E) :
    Blocks.ext (a + w) (fun κ => f (κ % 2 ^ w)) z = Blocks.ext w f (fun t => z (a + t)) := by
  rw [ext_rows a w]
  have h1 : ∀ i ∈ range (2 ^ a), Blocks.eqN a 0 z i *
      Blocks.ext w (fun c => f ((2 ^ w * i + c) % 2 ^ w)) (fun t => z (a + t)) =
      Blocks.eqN a 0 z i * Blocks.ext w f (fun t => z (a + t)) := by
    intro i _
    congr 1
    apply Blocks.ext_congr
    intro c hc
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
  rw [sum_congr rfl h1, ← sum_mul, sum_eqN, one_mul]

/-- **The extension of a vector that reads one field of bits.** -/
theorem ext_field (a w lo : ℕ) (f z : ℕ → E) :
    Blocks.ext (a + w + lo) (fun κ => f (κ / 2 ^ lo % 2 ^ w)) z =
      Blocks.ext w f (fun t => z (a + t)) := by
  rw [ext_dropLow (a + w) lo (fun m => f (m % 2 ^ w)) z, ext_dropHigh]

/-- **"All w bits are 1" gives the product of the coordinates.** -/
theorem ext_allOnes (w : ℕ) (z : ℕ → E) :
    Blocks.ext w (fun m => if m = 2 ^ w - 1 then 1 else 0) z = ∏ t ∈ range w, z t := by
  have hp : 0 < 2 ^ w := Nat.pos_of_ne_zero (by positivity)
  unfold Blocks.ext
  rw [sum_eq_single (2 ^ w - 1)]
  · beta_reduce
    rw [if_pos rfl, mul_one]
    unfold Blocks.eqN
    refine prod_congr rfl fun t ht => ?_
    have ht' := mem_range.1 ht
    rw [if_pos (by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true (by omega)), Nat.zero_add]
  · intro m _ hm
    beta_reduce
    rw [if_neg hm, mul_zero]
  · intro h
    exact absurd (mem_range.2 (by omega)) h

/-- **The top bit splits the extension.** -/
theorem ext_top (b : ℕ) (v z : ℕ → E) :
    Blocks.ext (1 + b) v z =
      (1 - z 0) * Blocks.ext b v (fun t => z (1 + t)) +
        z 0 * Blocks.ext b (fun c => v (2 ^ b + c)) (fun t => z (1 + t)) := by
  rw [ext_rows 1 b]
  have h2 : range (2 ^ 1) = {0, 1} := by decide
  rw [h2, sum_pair (by decide)]
  have e0 : Blocks.eqN 1 0 z 0 = 1 - z 0 := by simp [Blocks.eqN]
  have e1 : Blocks.eqN 1 0 z 1 = z 0 := by simp [Blocks.eqN]
  rw [e0, e1]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one]

end OnBytes.Ends

#print axioms OnBytes.Ends.unit_lin
#print axioms OnBytes.Ends.ext_field
#print axioms OnBytes.Ends.ext_allOnes
#print axioms OnBytes.Ends.ext_top
