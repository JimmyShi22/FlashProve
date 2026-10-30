-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Readable/Helpers.lean: the arithmetic of IntegerModel/Model.lean (its part 1, and
fits16 and normOk of its part 7) and its norm, shown equal to those of Inst/Model/Program.lean, of
Mathlib, or to an array `tabl n f` (IntegerModel/Runnable/Tools.lean); its rotary step, brought to a
formula; all under the hypotheses of the statements.
-/
import IntegerModel.Runnable.Attention
import IntegerModel.Runnable.FeedForward
import Inst.Model.Causal
import IntegerModel.Readable.Defs

set_option autoImplicit false

namespace IntegerModel.Readable

open Inst.Model IntegerModel.Runnable

/-! ## Part 1 of IntegerModel/Model.lean, and fits16 of its part 7 -/

/-- the model's one read function, on the array f 0, .., f (n - 1) -/
theorem tabl_entry {α : Type} [Inhabited α] {n : ℕ} (f : ℕ → α) {i : ℕ} (h : i < n) :
    (tabl n f).entry i = f i := by
  simp [Array.entry, tabl, Array.getD, h]

theorem tabulate_eq {α : Type} (n : ℕ) (f : ℕ → α) : IntegerTransformer.tabulate n f = tabl n f :=
  tabl_ofFn n f

theorem sumOver_eq (f : ℕ → ℤ) : ∀ n, IntegerTransformer.sumOver n f = ∑ j ∈ Finset.range n, f j
  | 0 => rfl
  | n + 1 => by
      show IntegerTransformer.sumOver n f + f n = _
      rw [sumOver_eq f n, Finset.sum_range_succ]

theorem maxUpTo_eq (f : ℕ → ℤ) : ∀ i, IntegerTransformer.maxUpTo f i = maxTo f i
  | 0 => rfl
  | i + 1 => by
      show max (IntegerTransformer.maxUpTo f i) (f (i + 1)) = max (maxTo f i) (f (i + 1))
      rw [maxUpTo_eq f i]

theorem firstArgmax_succ (f : ℕ → ℤ) : ∀ n, IntegerTransformer.firstArgmax f (n + 1) = argTo f n
  | 0 => by
      show (if f 0 < f 0 then 0 else 0) = 0
      exact ite_self _
  | n + 1 => by
      show (if f (IntegerTransformer.firstArgmax f (n + 1)) < f (n + 1) then n + 1
          else IntegerTransformer.firstArgmax f (n + 1)) =
        if f (argTo f n) < f (n + 1) then n + 1 else argTo f n
      rw [firstArgmax_succ f n]

theorem firstArgmax_eq (f : ℕ → ℤ) (n : ℕ) :
    IntegerTransformer.firstArgmax f n = argTo f (n - 1) := by
  cases n with
  | zero => rfl
  | succ n => exact firstArgmax_succ f n

theorem roundShift_eq (a : ℤ) (k : ℕ) : IntegerTransformer.roundShift a k = rhu a k := rfl
theorem clamp_eq (a b : ℤ) : IntegerTransformer.clamp a b = clamp b a := rfl
theorem lowByte_eq (a : ℤ) : IntegerTransformer.balancedLowByte a = lowByte a := rfl

theorem isqrt_eq (a : ℕ) : IntegerTransformer.integerSquareRoot a = Nat.sqrt a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    unfold IntegerTransformer.integerSquareRoot
    by_cases h0 : a = 0
    · rw [if_pos h0, h0]; rfl
    · rw [if_neg h0]
      simp only [ih (a / 4) (by omega)]
      have h1 : Nat.sqrt (a / 4) * Nat.sqrt (a / 4) ≤ a / 4 := Nat.sqrt_le (a / 4)
      have h2 : a / 4 < (Nat.sqrt (a / 4) + 1) * (Nat.sqrt (a / 4) + 1) := Nat.lt_succ_sqrt (a / 4)
      generalize Nat.sqrt (a / 4) = r at h1 h2 ⊢
      have e2 : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
      rw [e2] at h2
      by_cases hc : (2 * r + 1) * (2 * r + 1) ≤ a
      · rw [if_pos hc]
        refine Nat.eq_sqrt.2 ⟨hc, ?_⟩
        have e1 : (2 * r + 1 + 1) * (2 * r + 1 + 1) = 4 * (r * r) + 8 * r + 4 := by ring
        rw [e1]
        omega
      · rw [if_neg hc]
        refine Nat.eq_sqrt.2 ⟨?_, not_le.1 hc⟩
        have e1 : 2 * r * (2 * r) = 4 * (r * r) := by ring
        rw [e1]
        omega

theorem addVec_tabl (n : ℕ) (x y : Vec) :
    IntegerTransformer.addVectors (tabl n x) (tabl n y) = tabl n fun k => x k + y k := by
  unfold IntegerTransformer.addVectors
  rw [tabulate_eq, tabl_size]
  exact tabl_congr fun k hk => by rw [tabl_entry x hk, tabl_entry y hk]

theorem product_tabl (d : ℕ) (a : Vec) (W : Array (Array ℤ)) (n : ℕ) :
    IntegerTransformer.product (tabl d a) W n =
      tabl n fun j => dot d a fun k => (((W.entry k)).entry j) := by
  unfold IntegerTransformer.product
  rw [tabulate_eq, tabl_size]
  refine tabl_congr fun j _ => ?_
  rw [sumOver_eq]
  exact Finset.sum_congr rfl fun k hk => by rw [tabl_entry a (Finset.mem_range.1 hk)]

/-- a product with a weight matrix that holds the library's numbers inside its shape -/
theorem product_same (d : ℕ) (a : Vec) (W : Array (Array ℤ)) (n : ℕ) (w : Mat)
    (h : ∀ k < d, ∀ j < n, (((W.entry k)).entry j) = w k j) :
    IntegerTransformer.product (tabl d a) W n = tabl n fun j => dot d a fun k => w k j := by
  rw [product_tabl]
  exact tabl_congr fun j hj => dot_congr fun k hk => h k hk j hj

theorem fits16_iff (e : ℤ) : (decide (-32768 ≤ e) && decide (e ≤ 32767)) = true ↔ Fits16 e := by
  unfold Fits16
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  norm_num
  intro _
  omega

theorem fits16_tabl (n : ℕ) (f : Vec) :
    IntegerTransformer.fits16 (tabl n f) = true ↔ ∀ c < n, Fits16 (f c) :=
  (tabl_all _ _ _).trans (forall₂_congr fun _ _ => fits16_iff _)

/-! ## The norm -/

/-- the library's values of one norm, as the model's record -/
def normRec (np : NormPar) (d : ℕ) (x : Vec) : IntegerTransformer.Norm :=
  { sumSquares := NORM.V d x, root := NORM.sig np d x, reciprocal := NORM.R np d x,
    quotient := tabl d (NORM.yw np d x), out := tabl d (NORM.out np d x) }

theorem rmsNorm_eq (np : NormPar) (d : ℕ) (x : Vec) {bits shift : ℕ} {eps : ℤ} (hM : bits = np.M)
    (hK : shift = np.K) (he : eps = np.eps) :
    IntegerTransformer.rmsNorm bits shift eps (tabl d x) = normRec np d x := by
  subst hM hK he
  have h1 : IntegerTransformer.sumOver
        (tabl d x).size (fun k => ((tabl d x).entry k) * ((tabl d x).entry k)) = NORM.V d x := by
    rw [sumOver_eq, tabl_size]
    exact Finset.sum_congr rfl fun j hj => by
      rw [tabl_entry x (Finset.mem_range.1 hj)]; exact (sq (x j)).symm
  unfold IntegerTransformer.rmsNorm
  simp only [h1, isqrt_eq, tabl_map]
  rfl

theorem normOk_iff (np : NormPar) (d : ℕ) (x : Vec) {eps : ℤ} (he : eps = np.eps) :
    IntegerTransformer.normOk eps (normRec np d x) = true ↔ NORM.OK np d x := by
  subst he
  unfold IntegerTransformer.normOk normRec NORM.OK
  rw [Bool.and_eq_true, decide_eq_true_eq, fits16_tabl]

/-! ## The rotary step -/

theorem rotate_tabl (cosine sine : Array ℤ) (ch n : ℕ) (h2 : 2 ∣ ch) (hn : ch ∣ n) (F : Vec)
    (C S : ℕ → ℤ) (hC : ∀ j < ch / 2, (cosine.entry j) = C j)
    (hS : ∀ j < ch / 2, (sine.entry j) = S j) :
    IntegerTransformer.rotate cosine sine ch (tabl n F) = tabl n fun c =>
      if c % ch % 2 = 0 then C (c % ch / 2) * F c - S (c % ch / 2) * F (c + 1)
      else S (c % ch / 2) * F (c - 1) + C (c % ch / 2) * F c := by
  unfold IntegerTransformer.rotate
  rw [tabulate_eq, tabl_size]
  refine tabl_congr fun c hc => ?_
  have hch : 0 < ch := by
    rcases Nat.eq_zero_or_pos ch with h | h
    · subst h
      obtain ⟨a, rfl⟩ := hn
      simp at hc
    · exact h
  have hr := Nat.mod_lt c hch
  have hi : c % ch / 2 < ch / 2 := by omega
  have hpar : c % ch % 2 = c % 2 := Nat.mod_mod_of_dvd c h2
  show (if c % 2 = 0 then
        (cosine.entry (c % ch / 2)) * ((tabl n F).entry c) -
          (sine.entry (c % ch / 2)) * ((tabl n F).entry (c + 1))
      else
        (sine.entry (c % ch / 2)) * ((tabl n F).entry (c - 1)) +
          (cosine.entry (c % ch / 2)) * ((tabl n F).entry c)) = _
  rw [hpar, hC _ hi, hS _ hi, tabl_entry F hc]
  by_cases he : c % 2 = 0
  · rw [if_pos he, if_pos he, tabl_entry F (succ_lt_of_even h2 hn hc (hpar.trans he))]
  · rw [if_neg he, if_neg he, tabl_entry F (lt_of_le_of_lt (Nat.sub_le c 1) hc)]

end IntegerModel.Readable
