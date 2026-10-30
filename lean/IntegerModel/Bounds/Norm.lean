-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import IntegerModel.Bounds.Arithmetic

/-!
# Bounds at a norm

Two statements about vectors, `InBox` and `RowWithin`, and what holds at one norm:
- its result is in the box, whatever row it reads (`norm_out_inBox`);
- if the row is within a bound, coordinate by coordinate, and `normFits` passes for that bound,
  range conditions 1 and 2 hold at this norm (`normOk_of_normFits`). Condition 8 has no test of its
  own in the model's text: it follows from condition 1.

Proved for `eps ≥ 1`, which `wellFormed` asks for. Only Lean's core library is used.
-/

namespace IntegerTransformer.Bounds

/-- A vector in the box: every entry, and so every read, is in -2,047 .. 2,047. -/
def InBox (a : IntegerVector) : Prop := ∀ k, magnitude (a.entry k) ≤ activationBound

/-- A row of the stream within a bound, coordinate by coordinate. -/
def RowWithin (bound : Nat → Int) (x : IntegerVector) : Prop :=
  ∀ k, k < x.size → magnitude (x.entry k) ≤ bound k

/-- A vector whose entries were clamped to the activation bound is in the box. -/
theorem map_clamp_inBox (v : IntegerVector) : InBox (v.map fun e => clamp e activationBound) := by
  intro k
  by_cases inside : k < v.size
  · rw [map_read _ _ _ inside]; exact magnitude_clamp_le _ _ (by decide)
  · rw [entry_outside _ k (by rw [Array.size_map]; exact inside)]; decide

/-- A norm's result is in the box, whatever row the norm reads. -/
theorem norm_out_inBox (bits shift : Nat) (eps : Int) (x : IntegerVector) :
    InBox (rmsNorm bits shift eps x).out :=
  map_clamp_inBox _

/-- A norm's sum of squares is at most the sum of the squares of the row's bounds. -/
theorem norm_sumSquares_le (bits shift : Nat) (eps : Int) (x : IntegerVector) (bound : Nat → Int)
    (within : RowWithin bound x) :
    (rmsNorm bits shift eps x).sumSquares ≤ sumOver x.size fun k => bound k * bound k :=
  sumOver_le_sumOver _ _ _ fun k hk => square_le_square _ _ (within k hk)

/-- A norm's quotient: `|x[k]| ≤ root` and `root * reciprocal ≤ 2^bits + root / 2`, so the quotient
is at most `roundShift (2^bits + root / 2) shift` in absolute value. For `eps ≥ 1`; no condition on
the row. -/
theorem norm_quotient_le (bits shift : Nat) (eps : Int) (x : IntegerVector) (k : Nat) (inside : k < x.size)
    (eps_pos : 1 ≤ eps) :
    magnitude ((rmsNorm bits shift eps x).quotient.entry k) ≤
      roundShift (2 ^ bits + (rmsNorm bits shift eps x).root / 2) shift := by
  have rootPos := root_positive bits shift eps x eps_pos
  have made : (rmsNorm bits shift eps x).quotient =
      x.map fun xk => roundShift (xk * (rmsNorm bits shift eps x).reciprocal) shift := rfl
  have reciprocal : (rmsNorm bits shift eps x).reciprocal =
      (2 ^ bits + (rmsNorm bits shift eps x).root / 2) / (rmsNorm bits shift eps x).root := rfl
  have root : (rmsNorm bits shift eps x).root =
      integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat := rfl
  have term : x.entry k * x.entry k ≤ (rmsNorm bits shift eps x).sumSquares :=
    term_le_sumOver (fun k => x.entry k * x.entry k) (fun k => square_nonneg _) x.size k inside
  have spec := (isqrt_spec ((rmsNorm bits shift eps x).sumSquares + eps).toNat).2
  rw [made, map_read _ _ _ inside]
  apply magnitude_roundShift_le
  generalize (rmsNorm bits shift eps x).reciprocal = R at reciprocal
  generalize (rmsNorm bits shift eps x).root = σ at rootPos reciprocal root
  generalize (rmsNorm bits shift eps x).sumSquares = V at root term spec
  generalize x.entry k = a at term
  have small : -(σ + 1) < a ∧ a < σ + 1 := by
    apply bounded_of_square_lt a (σ + 1) (by omega)
    have cast : ((integerSquareRoot (V + eps).toNat + 1) * (integerSquareRoot (V + eps).toNat + 1) : Nat) =
        ((σ + 1) * (σ + 1) : Int) := by
      rw [root]; simp
    have : ((V + eps).toNat : Int) < (σ + 1) * (σ + 1) := by
      rw [← cast]; exact Int.ofNat_lt.mpr spec
    have nonneg := square_nonneg a
    omega
  have power : (0 : Int) < 2 ^ bits := Int.pow_pos (by decide)
  have product : R * σ ≤ 2 ^ bits + σ / 2 := by rw [reciprocal]; exact Int.ediv_mul_le _ (by omega)
  have Rnonneg : 0 ≤ R := by rw [reciprocal]; exact Int.ediv_nonneg (by omega) (by omega)
  have step : magnitude (a * R) ≤ σ * magnitude R :=
    magnitude_mul_le a R σ (by rw [magnitude_le_iff]; omega)
  have same : magnitude R = R := by unfold magnitude; omega
  rw [same] at step
  have swap : σ * R = R * σ := Int.mul_comm _ _
  omega

/-- Conditions 1 and 2 hold at a norm that reads a row within `bound`, if `normFits` passes for
`bound`. -/
theorem normOk_of_normFits (bits shift : Nat) (eps : Int) (x : IntegerVector) (bound : Nat → Int)
    (eps_pos : 1 ≤ eps) (within : RowWithin bound x)
    (fits : normFits bits shift eps x.size bound = true) :
    normOk eps (rmsNorm bits shift eps x) = true := by
  simp only [normFits, Bool.and_eq_true, decide_eq_true_eq] at fits
  have sum := norm_sumSquares_le bits shift eps x bound within
  simp only [normOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, ?_⟩
  apply fits16_of_bounded _ _ _ fits.2
  intro k inside
  rw [(size_rmsNorm bits shift eps x).1] at inside
  apply Int.le_trans (norm_quotient_le bits shift eps x k inside eps_pos)
  apply roundShift_le_roundShift
  have root : (rmsNorm bits shift eps x).root =
      integerSquareRoot ((rmsNorm bits shift eps x).sumSquares + eps).toNat := rfl
  have mono := isqrt_le_isqrt ((rmsNorm bits shift eps x).sumSquares + eps).toNat
    ((sumOver x.size fun k => bound k * bound k) + eps).toNat (by omega)
  rw [root]
  omega

end IntegerTransformer.Bounds
