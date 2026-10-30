-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/SumClosure.lean: what a caller of the sumcheck owes (`IsSum`,
OnBytes/Desc/First/P1/SumCore.lean) FOR A SUMMAND THAT IS BUILT UP, by sums and constants, from
products of two multilinear extensions. Algebra over a field. Definitions, statements and proofs.

A summand of a real protocol is seldom written as one list of terms: it is a sum over families,
layers and channels, under public constants, of products of two extensions. This file lets a caller
follow that text.

  `Lin n f`: on lists of n challenges f is the multilinear extension of some table. Closed under
    `add`, `sub`, `smul`, `sum` (over a Finset), `listSum`, `congr`; holds of constants (`const`)
    and of `mle` (`ofMle`).
  `Quad n f`: on lists of n challenges f is a finite sum, under constants, of products of two
    extensions. `Lin.mul`: the product of two `Lin`. Closed under `add`, `sub`, `smul`, `sum`,
    `listSum`, `ite`, `congr`; holds of 0 and of every `Lin`.
  `bitsK b`: a list of bits as field elements.
  `Quad.isSum`: A `Quad` SUMMAND IS SUMMED, by variables that are two-point with at least three
    coefficients, TO ITS OWN SUM OVER THE CUBE under the weights: `tot xs fun b => f (bitsK b)`.
  Tools: `IsSum.congr_len` (a summand is read at lists of the right length alone), `tot_congr_len`,
    `mle_const`, `mle_bits` (an extension at a corner is the table's entry).

Nothing is said of probabilities.
-/
import OnBytes.Desc.First.P1.PscProducts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open Polynomial

variable {K : Type} [Field K]

/-! ### Tools -/

/-- A summand is read at lists of the right length alone. -/
theorem IsSum.congr_len : ∀ {vs : List (Wt K)} {S T : List K → K} {c : K}, IsSum vs S c →
    (∀ rs, rs.length = vs.length → S rs = T rs) → IsSum vs T c
  | [], _, _, _, h, hS => by
    have e := hS [] rfl
    show _ = _
    rw [← e]
    exact h
  | _ :: _, _, _, _, ⟨q, hd, hs, hq⟩, hS =>
    ⟨q, hd, hs, fun x => (hq x).congr_len fun rs hl => hS (x :: rs) (by simp [hl])⟩

theorem tot_congr_len : ∀ (xs : List (K × K)) (F G : List Bool → K),
    (∀ b, b.length = xs.length → F b = G b) → tot xs F = tot xs G
  | [], _, _, h => h [] rfl
  | x :: xs, F, G, h => by
    show x.1 * tot xs _ + x.2 * tot xs _ = x.1 * tot xs _ + x.2 * tot xs _
    rw [tot_congr_len xs (fun b => F (false :: b)) (fun b => G (false :: b))
        (fun b hb => h (false :: b) (by simp [hb])),
      tot_congr_len xs (fun b => F (true :: b)) (fun b => G (true :: b))
        (fun b hb => h (true :: b) (by simp [hb]))]

theorem mle_const (c : K) : ∀ (n : ℕ) (rs : List K), rs.length = n → mle n (fun _ => c) rs = c
  | 0, _, _ => rfl
  | n + 1, [], h => by simp at h
  | n + 1, r :: rs, h => by
    show (1 - r) * mle n (fun _ => c) rs + r * mle n (fun _ => c) rs = c
    rw [mle_const c n rs (by simpa using h)]
    ring

/-- A list of bits as field elements. -/
def bitsK (b : List Bool) : List K := b.map fun x => if x then 1 else 0

theorem bitsK_length (b : List Bool) : (bitsK b : List K).length = b.length := List.length_map _

/-- An extension at a corner is the table's entry. -/
theorem mle_bits : ∀ (n : ℕ) (A : List Bool → K) (b : List Bool), b.length = n →
    mle n A (bitsK b) = A b
  | 0, _, [], _ => rfl
  | 0, _, _ :: _, h => by simp at h
  | n + 1, _, [], h => by simp at h
  | n + 1, A, x :: b, h => by
    have hb : b.length = n := by simpa using h
    show (1 - (if x then (1 : K) else 0)) * mle n (fun c => A (false :: c)) (bitsK b) +
      (if x then (1 : K) else 0) * mle n (fun c => A (true :: c)) (bitsK b) = A (x :: b)
    rw [mle_bits n _ b hb, mle_bits n _ b hb]
    cases x <;> simp

/-! ### One extension -/

/-- On lists of n challenges f is the multilinear extension of some table. -/
def Lin (n : ℕ) (f : List K → K) : Prop :=
  ∃ A : List Bool → K, ∀ rs, rs.length = n → f rs = mle n A rs

theorem Lin.ofMle (n : ℕ) (A : List Bool → K) : Lin n (mle n A) := ⟨A, fun _ _ => rfl⟩

theorem Lin.const (n : ℕ) (c : K) : Lin n fun _ => c :=
  ⟨fun _ => c, fun rs h => (mle_const c n rs h).symm⟩

theorem Lin.add {n : ℕ} {f g : List K → K} (hf : Lin n f) (hg : Lin n g) :
    Lin n fun rs => f rs + g rs := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨fun b => A b + B b, fun rs h => by
    beta_reduce
    rw [mle_add, hA rs h, hB rs h]⟩

theorem Lin.smul {n : ℕ} {f : List K → K} (c : K) (hf : Lin n f) : Lin n fun rs => c * f rs := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨fun b => c * A b, fun rs h => by
    beta_reduce
    rw [mle_smul, hA rs h]⟩

theorem Lin.congr {n : ℕ} {f g : List K → K} (hf : Lin n f)
    (h : ∀ rs, rs.length = n → g rs = f rs) : Lin n g := by
  obtain ⟨A, hA⟩ := hf
  exact ⟨A, fun rs hl => by rw [h rs hl, hA rs hl]⟩

theorem Lin.sub {n : ℕ} {f g : List K → K} (hf : Lin n f) (hg : Lin n g) :
    Lin n fun rs => f rs - g rs :=
  (hf.add (hg.smul (-1))).congr fun rs _ => by ring

theorem Lin.sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → List K → K)
    (h : ∀ i ∈ s, Lin n (f i)) : Lin n fun rs => ∑ i ∈ s, f i rs := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Lin.const n 0).congr fun rs _ => by simp
  | insert a s ha ih =>
    refine ((h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).congr fun rs _ => ?_
    rw [Finset.sum_insert ha]

theorem Lin.listSum {n : ℕ} {ι : Type} : ∀ (l : List ι) (f : ι → List K → K),
    (∀ i ∈ l, Lin n (f i)) → Lin n fun rs => (l.map fun i => f i rs).sum
  | [], _, _ => (Lin.const n 0).congr fun _ _ => by simp
  | a :: l, f, h =>
    ((h a (by simp)).add (Lin.listSum l f fun i hi => h i (by simp [hi]))).congr fun _ _ => by simp

/-! ### Sums of products of two -/

/-- On lists of n challenges f is a finite sum, under constants, of products of two extensions. -/
def Quad (n : ℕ) (f : List K → K) : Prop :=
  ∃ l : List (K × (List Bool → K) × (List Bool → K)), ∀ rs, rs.length = n →
    f rs = (l.map fun x => x.1 * (mle n x.2.1 rs * mle n x.2.2 rs)).sum

theorem Quad.congr {n : ℕ} {f g : List K → K} (hf : Quad n f)
    (h : ∀ rs, rs.length = n → g rs = f rs) : Quad n g := by
  obtain ⟨l, hl⟩ := hf
  exact ⟨l, fun rs hr => by rw [h rs hr, hl rs hr]⟩

theorem Quad.zero (n : ℕ) : Quad n fun _ => (0 : K) := ⟨[], fun _ _ => by simp⟩

/-- The product of two extensions. -/
theorem Lin.mul {n : ℕ} {f g : List K → K} (hf : Lin n f) (hg : Lin n g) :
    Quad n fun rs => f rs * g rs := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨[(1, A, B)], fun rs h => by simp [hA rs h, hB rs h]⟩

theorem Lin.quad {n : ℕ} {f : List K → K} (hf : Lin n f) : Quad n f :=
  (hf.mul (Lin.const n 1)).congr fun rs _ => by ring

theorem Quad.add {n : ℕ} {f g : List K → K} (hf : Quad n f) (hg : Quad n g) :
    Quad n fun rs => f rs + g rs := by
  obtain ⟨l, hl⟩ := hf
  obtain ⟨l', hl'⟩ := hg
  exact ⟨l ++ l', fun rs h => by
    beta_reduce
    rw [List.map_append, List.sum_append, hl rs h, hl' rs h]⟩

theorem Quad.smul {n : ℕ} {f : List K → K} (c : K) (hf : Quad n f) :
    Quad n fun rs => c * f rs := by
  obtain ⟨l, hl⟩ := hf
  refine ⟨l.map fun x => (c * x.1, x.2.1, x.2.2), fun rs h => ?_⟩
  beta_reduce
  rw [hl rs h, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  show c * (x.1 * (mle n x.2.1 rs * mle n x.2.2 rs)) = c * x.1 * (mle n x.2.1 rs * mle n x.2.2 rs)
  ring

theorem Quad.sub {n : ℕ} {f g : List K → K} (hf : Quad n f) (hg : Quad n g) :
    Quad n fun rs => f rs - g rs :=
  (hf.add (hg.smul (-1))).congr fun rs _ => by ring

theorem Quad.sum {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → List K → K)
    (h : ∀ i ∈ s, Quad n (f i)) : Quad n fun rs => ∑ i ∈ s, f i rs := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (Quad.zero n).congr fun rs _ => by simp
  | insert a s ha ih =>
    refine ((h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))).congr fun rs _ => ?_
    rw [Finset.sum_insert ha]

theorem Quad.listSum {n : ℕ} {ι : Type} : ∀ (l : List ι) (f : ι → List K → K),
    (∀ i ∈ l, Quad n (f i)) → Quad n fun rs => (l.map fun i => f i rs).sum
  | [], _, _ => (Quad.zero n).congr fun _ _ => by simp
  | a :: l, f, h =>
    ((h a (by simp)).add (Quad.listSum l f fun i hi => h i (by simp [hi]))).congr
      fun _ _ => by simp

theorem Quad.ite {n : ℕ} {f g : List K → K} (p : Prop) [Decidable p] (hf : Quad n f)
    (hg : Quad n g) : Quad n fun rs => if p then f rs else g rs := by
  by_cases hp : p
  · exact hf.congr fun rs _ => by rw [if_pos hp]
  · exact hg.congr fun rs _ => by rw [if_neg hp]

/-! ### The law -/

theorem isSum_list (vs : List (Wt K)) (xs : List (K × K)) (h : Twos 3 vs xs) :
    ∀ l : List (K × (List Bool → K) × (List Bool → K)),
      IsSum vs
        (fun rs => (l.map fun x => x.1 * (mle vs.length x.2.1 rs * mle vs.length x.2.2 rs)).sum)
        (tot xs fun b => (l.map fun x => x.1 * (x.2.1 b * x.2.2 b)).sum)
  | [] => by
    have hz := isSum_zero vs (twos_pos (by omega) vs xs h)
    refine hz.congr (fun _ => by simp) ?_
    have e : (tot xs fun _ : List Bool => (0 : K)) = 0 := by
      have := tot_smul (0 : K) xs fun _ => (0 : K)
      simpa using this
    simp only [List.map_nil, List.sum_nil]
    exact e.symm
  | x :: l => by
    have h1 := (isSum_mul vs xs x.2.1 x.2.2 h).smul x.1
    have h2 := isSum_list vs xs h l
    refine (h1.add h2).congr (fun _ => by simp) ?_
    rw [← tot_smul, ← tot_add]
    simp

/-- **A summand built up from products of two extensions is summed to its own sum over the
cube.** -/
theorem Quad.isSum {vs : List (Wt K)} {xs : List (K × K)} (h : Twos 3 vs xs) {f : List K → K}
    (hf : Quad vs.length f) : IsSum vs f (tot xs fun b => f (bitsK b)) := by
  obtain ⟨l, hl⟩ := hf
  have hlen : xs.length = vs.length := twos_length vs xs h
  have e : (tot xs fun b => f (bitsK b)) =
      tot xs fun b => (l.map fun x => x.1 * (x.2.1 b * x.2.2 b)).sum := by
    refine tot_congr_len xs _ _ fun b hb => ?_
    have hb' : b.length = vs.length := by rw [hb, hlen]
    rw [hl (bitsK b) (by rw [bitsK_length, hb'])]
    refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
    rw [mle_bits _ _ b hb', mle_bits _ _ b hb']
  rw [e]
  exact (isSum_list vs xs h l).congr_len fun rs hr => (hl rs hr).symm

end OnBytes.Desc.First.P1
