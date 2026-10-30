-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/MeetsPolicyIdleAtScales.lean

A ceiling on every token's logit gap, from the final norm's two exponents alone, and the policies
that exclude no output by its scores because of it. Theorems on the claim `MeetsPolicy`
(Policy/Front/MeetsPolicy.lean) and on the text of `IntegerTransformer.rmsNorm` and
`IntegerTransformer.trace` (IntegerModel/Model.lean), at all valid settings and all weights. No goal
of the library is stated here.

Below, a policy "excludes no output by its scores", at given settings and weights, if every output
that has scores (`HasScores`) and meets clause (c) of `MeetsPolicy` meets it. Neither of these two
reads the policy. Clause (c): a token after a full window is the model's next token. The theorems
here say it of all weights at once.

The point. A token's cost is its logit gap plus 2^8. A logit is the final norm's output row times a
column of the output matrix. An entry of that matrix is in -4096 .. 4095 by the type `ModelWeights`,
so two logits of one row differ by at most 8191 times the sum of the absolute values of the norm's
output row. That sum is bounded whatever the row that enters the norm: the norm scales it to a
length of at most about 2^(MF - KF + 1), where MF and KF are the settings' `finalBits` and
`finalShift` (the lines MF and KF of a parameter file). Whoever writes the parameter file picks
these two numbers. So at a small difference MF - KF every gap stays below a low ceiling, under every
model, and a policy whose theta and C are both at least 2^8 plus that ceiling bounds no counted
token's score: it excludes no output by its scores. In this file "the ceiling" is always the ceiling
on a gap; a cost is at most 2^8 plus the ceiling.

Main names.
* `gapCeiling bits shift` = 8191 (144 2^(bits - shift) + 2560) + 1: the ceiling on a gap.
* `NormOutput.sum_abs_rmsNorm_out_le`: for 1 ≤ eps and 7 ≤ shift ≤ bits, the absolute values of a
  norm's output, on a row of at most 5,120 entries, sum to at most 144 2^(bits - shift) + 2560.
* `logitGap_le_gapCeiling`: at valid settings, under all weights, after 1 to 1,024 tokens of the
  vocabulary, no token of the vocabulary has a gap above the ceiling.
* `outputCost_le_gapCeiling`: at valid settings, under all weights, in an output that has scores, no
  output token costs more than 2^8 plus the ceiling.
* `meetsPolicy_iff_of_gapCeiling_le`: at valid settings, at a policy with 2^8 + ceiling ≤ theta and
  2^8 + ceiling ≤ C, whatever cap is (0 too), the claim says only that the output has scores and
  that a token after a full window is the model's next token.
* `meetsPolicy_of_close_scales`: at valid settings with MF ≤ KF + 11 that holds at every policy with
  2,436,593,409 ≤ theta and 2,436,593,409 ≤ C. This number is below 3 · 2^30
  (`gapCeiling_lt_of_close`), and so below 2^32.
* `exists_policy_of_close_scales`: so at valid settings with MF ≤ KF + 11 there is a policy with
  2^8 ≤ theta < C < 2^32 and cap = 0 that excludes no output by its scores. Of its policy a lawful
  table of scales asks C < 2^32, theta ≤ C and cap ≤ 1,024 (`Inst.Model.Lawful`,
  Inst/Model/Scales.lean).

Limits.
* The ceiling is an upper bound. No theorem here says that some weights reach it: a policy below it
  may exclude no output by its scores as well. How near made-up weights come at one pair of
  exponents: Policy/Front/TeethAllChannels.lean has a cost of 9,603,783,936 at MF = 44 and KF = 30,
  where 2^8 plus the ceiling is 19,345,962,753.
* The least value of 2^8 + ceiling, at MF = KF, is 22,148,721. About a policy with theta or C below
  it, the policy (25856, 512, 1) of the second named set of public files (`zGap`,
  Ladder/Stored.lean) among them, this file says nothing at any scales.
* For MF - KF = 12, 13 or 14 the number 2^8 + ceiling is above 2^32, and this file says nothing
  about a policy with C < 2^32. The two named sets of public files have MF = 44 and KF = 30
  (`storedLines`, Ladder/Stored.lean). The border 11 is this bound's. For the differences 12 to 14
  whether some policy with theta < C < 2^32 excludes no output by its scores under all weights is
  open here, but for the settings of the reference scales (Policy/Front/TeethAllChannels.lean; at
  what the library's reader returns at the two named sets of public files:
  Johnson/Goal/Files/MeetsPolicyAtFiles.lean); by hand it depends on MF too, not only on the
  difference.
* That the premises of `meetsPolicy_of_close_scales` can be met together is no theorem here. By
  hand: `settingsAreValid_of_final` gives valid settings with MF ≤ KF + 11, and under the all-zero
  weights outputs have scores at all valid settings (`meetsPolicy_zeroWeights`,
  Policy/Front/TrueUnder.lean). Under these weights every policy with 257 ≤ theta and 257 ≤ C is met
  anyway. No weights with a cost near the ceiling are shown to have scores at such settings.
* No theorem here says that a parameter file with MF ≤ KF + 11 is accepted by the library's reader
  of the public files or is in the scope of its goals (`readFiles`, `InScope`, Ladder.lean).
  Evaluated, not proved, at three such sets of files, two at exact match and one at the policy of
  `exists_policy_of_close_scales`: Johnson/Goal/Files/ScopeAtNarrowNorm.lean. Valid settings allow
  every difference from 0 to 14 (`normInRange`, VerifiableInference/ModelWeights.lean;
  `settingsAreValid_of_final` below).
* As everywhere for this claim: the unit of a gap is that of the given weights' own integer logits;
  and the number of counted tokens is that of one output, which in a soundness statement the prover
  picks and may cut.
* The constants 144 and 2560 are for rows of at most 5,120 entries, the width at valid settings.
* Nothing here speaks of a protocol, a commitment, a prover or a verifier.

Terms: lean/GLOSSARY.md.

-/
import Policy.Front.MeetsPolicyBounds
import IntegerModel.Readable.Reads

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference

/- The lemmas of parts 1 to 3 speak of whole numbers and of `IntegerTransformer`, not of a policy.
They stand in a namespace of their own, so that their short names meet no other file's. -/
namespace NormOutput

/-! ## 1. Whole numbers -/

/-- The norm's reciprocal times its root plus 1. If c r ≤ P + q with 2 q ≤ r, as for the rounded
quotient c = (P + r / 2) / r, then c (r + 1) ≤ 2 P + 1. -/
theorem reciprocal_mul_succ_le {P r c q : ℤ} (root : 1 ≤ r) (nonneg : 0 ≤ c) (power : 0 ≤ P)
    (half : 2 * q ≤ r) (quotient : c * r ≤ P + q) : c * (r + 1) ≤ 2 * P + 1 := by
  by_cases zero : c ≤ 0
  · have e : c = 0 := le_antisymm zero nonneg
    rw [e, zero_mul]
    linarith
  · have one : 1 ≤ c := by omega
    have product : 0 ≤ (r - 1) * (c - 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [product]

/-- 144 s |a| ≤ 5184 a^2 + s^2: the square of 72 |a| - s is not negative. Summed over at most
5,120 ≤ 72^2 entries it bounds a sum of absolute values by the sum of squares. -/
theorem abs_le_square_add (a s : ℤ) : 144 * s * |a| ≤ 5184 * (a * a) + s * s := by
  have square := sq_nonneg (72 * |a| - s)
  have same : |a| * |a| = a * a := abs_mul_abs_self a
  nlinarith [square, same]

/-- The clamp does not raise an absolute value. -/
theorem abs_clamp_le (w : ℤ) :
    |IntegerTransformer.clamp w IntegerTransformer.activationBound| ≤ |w| := by
  have h1 := le_abs_self w
  have h2 := neg_abs_le w
  have h3 := abs_nonneg w
  rw [abs_le]
  unfold IntegerTransformer.clamp IntegerTransformer.activationBound
  generalize |w| = t at h1 h2 h3 ⊢
  constructor <;> omega

/-- A number that is divided by 2^(j + 1), rounded and clamped: 2^(j + 1) times the absolute value
of the result is at most the number's absolute value plus 2^j. -/
theorem abs_clamp_roundShift_le (a : ℤ) (j : ℕ) :
    2 * 2 ^ j * |IntegerTransformer.clamp (IntegerTransformer.roundShift a (j + 1))
        IntegerTransformer.activationBound| ≤ |a| + 2 ^ j := by
  obtain ⟨low, high⟩ := IntegerTransformer.roundShift_spec a (j + 1)
  have clamped := abs_clamp_le (IntegerTransformer.roundShift a (j + 1))
  rw [Nat.add_sub_cancel, pow_succ] at low high
  have positive : (0 : ℤ) < 2 ^ j := by positivity
  generalize IntegerTransformer.roundShift a (j + 1) = w at low high clamped ⊢
  generalize |IntegerTransformer.clamp w IntegerTransformer.activationBound| = z at clamped ⊢
  generalize (2 : ℤ) ^ j = H at low high positive ⊢
  have h1 := le_abs_self a
  have h2 := neg_abs_le a
  have wide : |w * (H * 2)| ≤ |a| + H := by
    rw [abs_le]
    constructor
    · nlinarith [high]
    · linarith
  have split : |w * (H * 2)| = 2 * H * |w| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℤ) < H * 2)]
    ring
  have scaled : 2 * H * z ≤ 2 * H * |w| := mul_le_mul_of_nonneg_left clamped (by linarith)
  linarith

/-- A termwise bound, summed. -/
theorem mul_sumOver_le {n : ℕ} {f g : ℕ → ℤ} {A B D : ℤ}
    (term : ∀ k < n, A * f k ≤ B * g k + D) :
    A * IntegerTransformer.sumOver n f ≤ B * IntegerTransformer.sumOver n g + n * D := by
  induction n with
  | zero => simp [IntegerTransformer.sumOver]
  | succ n ih =>
    have below := ih fun k hk => term k (Nat.lt_succ_of_lt hk)
    have last := term n (Nat.lt_succ_self n)
    simp only [IntegerTransformer.sumOver]
    push_cast
    nlinarith [below, last]

/-- Two sums of products with the same first factors differ by at most M times the sum of these
factors' absolute values, if the second factors differ by at most M. -/
theorem sumOver_mul_sub_le {n : ℕ} {o a b : ℕ → ℤ} {M : ℤ}
    (near : ∀ k, a k - b k ≤ M ∧ b k - a k ≤ M) :
    IntegerTransformer.sumOver n (fun k => o k * a k) -
        IntegerTransformer.sumOver n (fun k => o k * b k) ≤
      M * IntegerTransformer.sumOver n (fun k => |o k|) := by
  induction n with
  | zero => simp [IntegerTransformer.sumOver]
  | succ n ih =>
    have last : o n * (a n - b n) ≤ |o n| * M :=
      calc o n * (a n - b n) ≤ |o n * (a n - b n)| := le_abs_self _
        _ = |o n| * |a n - b n| := abs_mul _ _
        _ ≤ |o n| * M :=
          mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith [(near n).2], (near n).1⟩)
            (abs_nonneg _)
    simp only [IntegerTransformer.sumOver]
    nlinarith [ih, last]

/-- The last step of the bound on a norm's output, on whole numbers: s is the root plus 1, c the
reciprocal, H = 2^(shift - 1), E = 2^(bits - shift), Q the sum of squares, S the sum of the output's
absolute values, n the number of entries. -/
theorem sum_le_of_summed {s c H E Q S n : ℤ} (positive : 0 < s) (nonneg : 0 ≤ c) (half : 64 ≤ H)
    (power : 1 ≤ E) (reciprocal : c * s ≤ 2 * (E * (2 * H)) + 1) (squares : Q ≤ s * s)
    (entries : n ≤ 5120)
    (summed : 144 * s * (2 * H) * S ≤ 5184 * c * Q + n * (c * (s * s) + 144 * s * H)) :
    S ≤ 144 * E + 2560 := by
  have t1 : c * Q ≤ c * (s * s) := mul_le_mul_of_nonneg_left squares nonneg
  have each : 0 ≤ c * (s * s) + 144 * s * H :=
    add_nonneg (mul_nonneg nonneg (mul_nonneg positive.le positive.le))
      (mul_nonneg (mul_nonneg (by norm_num) positive.le) (by linarith))
  have t2 : n * (c * (s * s) + 144 * s * H) ≤ 5120 * (c * (s * s) + 144 * s * H) :=
    mul_le_mul_of_nonneg_right entries each
  have t3 : s * (288 * H * S) ≤ s * (10304 * (c * s) + 737280 * H) := by nlinarith [t1, t2, summed]
  have t4 : 288 * H * S ≤ 10304 * (c * s) + 737280 * H := le_of_mul_le_mul_left t3 positive
  by_contra above
  have more : 144 * E + 2561 ≤ S := by omega
  have t5 : 288 * H * (144 * E + 2561) ≤ 288 * H * S :=
    mul_le_mul_of_nonneg_left more (by linarith)
  have t6 : 64 * 1 ≤ H * E := mul_le_mul half power (by norm_num) (by linarith)
  nlinarith [t4, t5, t6, reciprocal]

/-! ## 2. The norm -/

/-- The bound on a norm's output, for functions in place of arrays: `x` is the row, `r` the root,
`c` the reciprocal, `out` the result. -/
theorem sum_abs_le_of_norm {n : ℕ} {x out : ℕ → ℤ} {c r : ℤ} {bits shift : ℕ} (size_le : n ≤ 5120)
    (shift_ge : 7 ≤ shift) (shift_le : shift ≤ bits) (root : 1 ≤ r)
    (reciprocal : c = (2 ^ bits + r / 2) / r)
    (squares : IntegerTransformer.sumOver n (fun k => x k * x k) < (r + 1) * (r + 1))
    (made : ∀ k < n, out k = IntegerTransformer.clamp
      (IntegerTransformer.roundShift (x k * c) shift) IntegerTransformer.activationBound) :
    IntegerTransformer.sumOver n (fun k => |out k|) ≤ 144 * 2 ^ (bits - shift) + 2560 := by
  have power : (0 : ℤ) ≤ 2 ^ bits := by positivity
  have nonneg : 0 ≤ c := by
    rw [reciprocal]
    exact Int.ediv_nonneg (add_nonneg power (Int.ediv_nonneg (by omega) (by norm_num))) (by omega)
  have quotient : c * r ≤ 2 ^ bits + r / 2 := by
    rw [reciprocal]
    exact Int.ediv_mul_le _ (by omega)
  have product : c * (r + 1) ≤ 2 * 2 ^ bits + 1 :=
    reciprocal_mul_succ_le root nonneg power (by omega) quotient
  obtain ⟨j, rfl⟩ : ∃ j, shift = j + 1 := ⟨shift - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, bits = j + 1 + d := ⟨bits - (j + 1), by omega⟩
  have difference : j + 1 + d - (j + 1) = d := by omega
  have powers : (2 : ℤ) ^ (j + 1 + d) = 2 ^ d * (2 * 2 ^ j) := by ring
  have half : (64 : ℤ) ≤ 2 ^ j :=
    calc (64 : ℤ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
  have one : (1 : ℤ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have term : ∀ k < n, 144 * (r + 1) * (2 * 2 ^ j) * |out k| ≤
      5184 * c * (x k * x k) + (c * ((r + 1) * (r + 1)) + 144 * (r + 1) * 2 ^ j) := by
    intro k hk
    rw [made k hk]
    have rounded := abs_clamp_roundShift_le (x k * c) j
    rw [abs_mul, abs_of_nonneg nonneg] at rounded
    have square := abs_le_square_add (x k) (r + 1)
    generalize |IntegerTransformer.clamp (IntegerTransformer.roundShift (x k * c) (j + 1))
      IntegerTransformer.activationBound| = z at rounded ⊢
    have m1 := mul_le_mul_of_nonneg_left rounded (by linarith : (0 : ℤ) ≤ 144 * (r + 1))
    have m2 := mul_le_mul_of_nonneg_left square nonneg
    nlinarith [m1, m2]
  have summed := mul_sumOver_le (f := fun k => |out k|) (g := fun k => x k * x k) term
  rw [difference]
  rw [powers] at product
  exact sum_le_of_summed (by linarith) nonneg half one product squares.le
    (by exact_mod_cast size_le) summed

/-- **For 1 ≤ eps and 7 ≤ shift ≤ bits, whatever the row of at most 5,120 entries, the absolute
values of a norm's output sum to at most 144 · 2^(bits - shift) + 2560.** Why: the reciprocal times
the root plus 1 is at most 2^(bits + 1) + 1, so before rounding the output has a Euclidean length
below about 2^(bits - shift + 1); a row of 5,120 entries of that length has absolute values that sum
to at most 72 times the length; and rounding adds at most 1/2 for each entry. -/
theorem sum_abs_rmsNorm_out_le (bits shift : ℕ) (eps : ℤ) (x : IntegerTransformer.IntegerVector)
    (eps_pos : 1 ≤ eps) (shift_ge : 7 ≤ shift) (shift_le : shift ≤ bits)
    (size_le : x.size ≤ 5120) :
    IntegerTransformer.sumOver x.size
        (fun k => |(IntegerTransformer.rmsNorm bits shift eps x).out.entry k|) ≤
      144 * 2 ^ (bits - shift) + 2560 := by
  have nonneg : 0 ≤ IntegerTransformer.sumOver x.size fun k => x.entry k * x.entry k :=
    IntegerTransformer.sumOver_nonneg _ (fun k => IntegerTransformer.square_nonneg _) _
  have spec := (IntegerTransformer.isqrt_spec
    (IntegerTransformer.sumOver x.size (fun k => x.entry k * x.entry k) + eps).toNat).2
  refine sum_abs_le_of_norm (x := fun k => x.entry k)
    (out := fun k => (IntegerTransformer.rmsNorm bits shift eps x).out.entry k)
    (c := (IntegerTransformer.rmsNorm bits shift eps x).reciprocal)
    (r := (IntegerTransformer.rmsNorm bits shift eps x).root) size_le shift_ge shift_le
    (IntegerTransformer.root_positive bits shift eps x eps_pos) rfl ?_ ?_
  · show IntegerTransformer.sumOver x.size (fun k => x.entry k * x.entry k) <
      (((IntegerTransformer.integerSquareRoot
          (IntegerTransformer.sumOver x.size (fun k => x.entry k * x.entry k) + eps).toNat : ℕ) :
          ℤ) + 1) *
        (((IntegerTransformer.integerSquareRoot
          (IntegerTransformer.sumOver x.size (fun k => x.entry k * x.entry k) + eps).toNat : ℕ) :
          ℤ) + 1)
    generalize IntegerTransformer.sumOver x.size (fun k => x.entry k * x.entry k) = V
      at nonneg spec ⊢
    generalize IntegerTransformer.integerSquareRoot (V + eps).toNat = i at spec ⊢
    have cast : (((V + eps).toNat : ℕ) : ℤ) < ((i : ℤ) + 1) * ((i : ℤ) + 1) := by
      exact_mod_cast spec
    have back : (((V + eps).toNat : ℕ) : ℤ) = V + eps := Int.toNat_of_nonneg (by linarith)
    rw [back] at cast
    linarith
  · intro k hk
    show (IntegerTransformer.rmsNorm bits shift eps x).out.entry k =
      IntegerTransformer.clamp (IntegerTransformer.roundShift
        (x.entry k * (IntegerTransformer.rmsNorm bits shift eps x).reciprocal) shift)
        IntegerTransformer.activationBound
    have made : (IntegerTransformer.rmsNorm bits shift eps x).out =
        (x.map fun xk => IntegerTransformer.roundShift
          (xk * (IntegerTransformer.rmsNorm bits shift eps x).reciprocal) shift).map
          fun wk => IntegerTransformer.clamp wk IntegerTransformer.activationBound := rfl
    rw [made, IntegerTransformer.map_read _ _ _ (by rw [Array.size_map]; exact hk),
      IntegerTransformer.map_read _ _ _ hk]

/-! ## 3. The output matrix and the logits -/

/-- Every read of a matrix whose entries are within `low .. high` is within these, if 0 is: a read
outside the matrix gives 0. -/
theorem entry_within {low high : ℤ} {matrix : IntegerTransformer.Matrix}
    (within : entriesWithin low high matrix = true) (zero : low ≤ 0 ∧ 0 ≤ high) (k v : ℕ) :
    low ≤ (matrix.entry k).entry v ∧ (matrix.entry k).entry v ≤ high := by
  simp only [entriesWithin, Array.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at within
  by_cases hk : k < matrix.size
  · rw [IntegerTransformer.entry_inside matrix k hk]
    by_cases hv : v < matrix[k].size
    · rw [IntegerTransformer.entry_inside matrix[k] v hv]
      exact within k hk v hv
    · rw [IntegerTransformer.entry_outside matrix[k] v hv]
      exact zero
  · rw [IntegerTransformer.entry_outside matrix k hk, entry_default v]
    exact zero

/-- An entry of a row vector times a matrix. -/
theorem product_entry (o : IntegerTransformer.IntegerVector) (W : IntegerTransformer.Matrix) {V v : ℕ}
    (h : v < V) :
    (IntegerTransformer.product o W V).entry v =
      IntegerTransformer.sumOver o.size fun k => o.entry k * (W.entry k).entry v := by
  unfold IntegerTransformer.product
  exact IntegerTransformer.tabulate_read _ _ _ h

/-- Two entries of a row vector times a matrix of 13-bit weights differ by at most 8191 times the
sum of the vector's absolute values. -/
theorem product_entry_sub_le (o : IntegerTransformer.IntegerVector) {W : IntegerTransformer.Matrix}
    (within : entriesWithin (-4096) 4095 W = true) {V a b : ℕ} (ha : a < V) (hb : b < V) :
    (IntegerTransformer.product o W V).entry a - (IntegerTransformer.product o W V).entry b ≤
      8191 * IntegerTransformer.sumOver o.size (fun k => |o.entry k|) := by
  rw [product_entry o W ha, product_entry o W hb]
  refine sumOver_mul_sub_le (o := fun k => o.entry k) (a := fun k => (W.entry k).entry a)
    (b := fun k => (W.entry k).entry b) fun k => ?_
  have h1 := entry_within within ⟨by norm_num, by norm_num⟩ k a
  have h2 := entry_within within ⟨by norm_num, by norm_num⟩ k b
  show (W.entry k).entry a - (W.entry k).entry b ≤ 8191 ∧
    (W.entry k).entry b - (W.entry k).entry a ≤ 8191
  constructor <;> omega

/-- For arguments that fit together and a prompt, the logits at a position are the final norm of the
last stream's row, times the output matrix. -/
theorem trace_logits_entry (s : IntegerTransformer.Settings) (tables : IntegerTransformer.Tables)
    (weights : IntegerTransformer.Weights) (prompt : Array Nat)
    (formed : IntegerTransformer.wellFormed s tables weights = true)
    (prompt_ok : IntegerTransformer.isPrompt s prompt = true) {t : ℕ} (ht : t < prompt.size) :
    (IntegerTransformer.trace s tables weights prompt).logits.entry t =
      IntegerTransformer.product
        (IntegerTransformer.rmsNorm s.finalBits s.finalShift s.finalEps
          ((IntegerTransformer.trace s tables weights prompt).last.entry t)).out
        weights.head s.vocabulary := by
  have rows := (IntegerTransformer.trace_shape s tables weights prompt formed prompt_ok).2.2.2.1.1
  have made : (IntegerTransformer.trace s tables weights prompt).logits =
      ((IntegerTransformer.trace s tables weights prompt).last.map fun row =>
        IntegerTransformer.rmsNorm s.finalBits s.finalShift s.finalEps row).map
        fun norm => IntegerTransformer.product norm.out weights.head s.vocabulary := rfl
  rw [made, IntegerTransformer.map_read _ _ _ (by rw [Array.size_map, rows]; exact ht),
    IntegerTransformer.map_read _ _ _ (by rw [rows]; exact ht)]

/-- If no token's logit lies more than `spread` above the logit of `token`, the gap of `token` is at
most spread + 1. The 1 is what the gap adds for a smaller token. (`logitGap_le_of_close`,
Policy/Front/MeetsPolicyBounds.lean, says the same; this file takes one theorem alone from that
file, `meetsPolicy_of_costs_le`.) -/
theorem logitGap_le_of_differences {vocabulary : ℕ} {logits : IntegerTransformer.IntegerVector}
    {token : Token} {spread : ℤ}
    (near : ∀ other ≤ vocabulary - 1, logits.entry other - logits.entry token ≤ spread) :
    logitGap vocabulary logits token ≤ spread + 1 := by
  obtain ⟨-, other, inside, attained⟩ := IntegerTransformer.maxUpTo_spec
    (fun other => logits.entry other - logits.entry token + if other < token then 1 else 0)
    (vocabulary - 1)
  have close := near other inside
  have step : logits.entry other - logits.entry token + (if other < token then 1 else 0) ≤
      spread + 1 := by
    split <;> linarith
  exact (le_of_eq attained.symm).trans step

/-- What this file reads of valid settings: the width, and three of the ranges of the final norm's
numbers. -/
theorem final_of_valid {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) :
    settings.width = 5120 ∧ 1 ≤ settings.finalEps ∧ 17 ≤ settings.finalShift ∧
      settings.finalShift ≤ settings.finalBits := by
  simp only [settingsAreValid, hasModelSizes, settingsInRange, normInRange, Bool.and_eq_true,
    beq_iff_eq, decide_eq_true_eq] at valid
  obtain ⟨⟨sizes, ranges, -⟩, -⟩ := valid
  exact ⟨by omega, by omega, by omega, by omega⟩

end NormOutput

open NormOutput

/-! ## 4. The ceiling on a gap and on a cost -/

/-- The ceiling on a logit gap at a final norm with the exponents `bits` (MF) and `shift` (KF), at
the width 5,120 and 13-bit weights in the output matrix. A shorthand for this file's statements; it
states no goal. The subtraction is that of natural numbers; valid settings have shift ≤ bits. -/
def gapCeiling (bits shift : ℕ) : ℤ :=
  8191 * (144 * 2 ^ (bits - shift) + 2560) + 1

variable {settings : IntegerTransformer.Settings}

/-- **At valid settings, under all weights, after 1 to 1,024 tokens of the vocabulary, every token
of the vocabulary has a gap of at most `gapCeiling settings.finalBits settings.finalShift`.** No
range condition of the integer program is asked: the model need not have a value on these tokens. -/
theorem logitGap_le_gapCeiling (valid : settingsAreValid settings = true)
    (weights : ModelWeights settings) {tokens : List Token}
    (prompt_ok : IntegerTransformer.isPrompt settings tokens.toArray = true) {token : Token}
    (small : token < settings.vocabulary) :
    logitGap settings.vocabulary (modelLogits settings weights tokens) token ≤
      gapCeiling settings.finalBits settings.finalShift := by
  obtain ⟨width, eps_pos, shift_ge, shift_le⟩ := final_of_valid valid
  have ok : weightsAreValid settings weights.val = true := weights.property
  unfold weightsAreValid at ok
  rw [Bool.and_eq_true] at ok
  obtain ⟨formed, ranges⟩ := ok
  unfold weightsInRange at ranges
  rw [Bool.and_eq_true, Bool.and_eq_true] at ranges
  have within := ranges.1.2
  have some_token := (IntegerTransformer.isPrompt_spec settings tokens.toArray prompt_ok).1
  have ht : tokens.length - 1 < tokens.toArray.size := by
    rw [List.size_toArray] at some_token ⊢
    omega
  have row := (IntegerTransformer.trace_shape settings lookupTables weights.val tokens.toArray
    formed prompt_ok).2.2.2.1.2 _ ht
  have logits : modelLogits settings weights tokens = _ :=
    trace_logits_entry settings lookupTables weights.val tokens.toArray formed prompt_ok ht
  have short := sum_abs_rmsNorm_out_le settings.finalBits settings.finalShift settings.finalEps
    ((IntegerTransformer.trace settings lookupTables weights.val tokens.toArray).last.entry
      (tokens.length - 1)) eps_pos (by omega) shift_le (le_of_eq (row.trans width))
  have scaled := mul_le_mul_of_nonneg_left short (by norm_num : (0 : ℤ) ≤ 8191)
  have some_entry : 0 < settings.vocabulary := Nat.lt_of_le_of_lt (Nat.zero_le _) small
  unfold gapCeiling
  refine logitGap_le_of_differences fun other inside => ?_
  rw [logits]
  have near := product_entry_sub_le
    (IntegerTransformer.rmsNorm settings.finalBits settings.finalShift settings.finalEps
      ((IntegerTransformer.trace settings lookupTables weights.val tokens.toArray).last.entry
        (tokens.length - 1))).out within (show other < settings.vocabulary by omega) small
  rw [(IntegerTransformer.size_rmsNorm _ _ _ _).2] at near
  exact le_trans near scaled

/-- **At valid settings, under all weights, in an output that has scores, no output token costs more
than 2^8 plus `gapCeiling settings.finalBits settings.finalShift`.** -/
theorem outputCost_le_gapCeiling (valid : settingsAreValid settings = true)
    {weights : ModelWeights settings} {prompt output : List Token}
    (scores : HasScores settings weights prompt output) {position : ℕ}
    (h : position < output.length) :
    outputCost settings weights prompt output position ≤
      2 ^ 8 + gapCeiling settings.finalBits settings.finalShift := by
  have prompt_ok := (model_of_isSome settings lookupTables weights.val
    (prompt ++ output.take position).toArray (scores.defined position h)).1.2
  have small : output.getD position 0 < settings.vocabulary := by
    rw [List.getD_eq_getElem _ _ h]
    exact scores.inVocabulary _ (List.mem_append_right _ (List.getElem_mem h))
  have gap := logitGap_le_gapCeiling valid weights prompt_ok small
  unfold outputCost tokenCost
  linarith

/-! ## 5. The policies that exclude no output by its scores for this reason -/

/-- **At valid settings a policy whose C and theta are both at least 2^8 plus the ceiling excludes
no output by its scores, whatever the weights and whatever cap is.** That is: under all weights,
every output that has scores and meets clause (c) of `MeetsPolicy` (a token after a full window is
the model's next token) meets the policy, at cap = 0 too. The ceiling is
`gapCeiling settings.finalBits settings.finalShift`: it depends on the final norm's two exponents
alone, which whoever writes the parameter file picks. -/
theorem meetsPolicy_of_gapCeiling_le (valid : settingsAreValid settings = true)
    {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings} {prompt output : List Token}
    (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
      settings.positions ≤ prompt.length + position →
        modelNextToken settings weights (prompt ++ output.take position) = some output[position])
    (clip : 2 ^ 8 + gapCeiling settings.finalBits settings.finalShift ≤ (policy.C : ℤ))
    (mean : 2 ^ 8 + gapCeiling settings.finalBits settings.finalShift ≤ (policy.theta : ℤ)) :
    MeetsPolicy settings policy weights prompt output :=
  meetsPolicy_of_costs_le scores after clip mean fun position counted =>
    outputCost_le_gapCeiling valid scores (by unfold countedTokens at counted; omega)

/-- **At valid settings, at a policy whose C and theta are both at least 2^8 plus the ceiling, under
any weights, an output meets the policy exactly if it has scores and meets clause (c)**, whatever
cap is. No counted token's score is bounded by such a policy. The ceiling is
`gapCeiling settings.finalBits settings.finalShift`; clause (c) of `MeetsPolicy`: a token after a
full window is the model's next token. -/
theorem meetsPolicy_iff_of_gapCeiling_le (valid : settingsAreValid settings = true)
    {policy : Inst.Model.AcceptancePolicy} (weights : ModelWeights settings) (prompt output : List Token)
    (clip : 2 ^ 8 + gapCeiling settings.finalBits settings.finalShift ≤ (policy.C : ℤ))
    (mean : 2 ^ 8 + gapCeiling settings.finalBits settings.finalShift ≤ (policy.theta : ℤ)) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
        ∀ position (h : position < output.length),
          settings.positions ≤ prompt.length + position →
            modelNextToken settings weights (prompt ++ output.take position) =
              some output[position] :=
  ⟨fun h => ⟨h.toHasScores, h.afterFullWindow⟩,
    fun h => meetsPolicy_of_gapCeiling_le valid h.1 h.2 clip mean⟩

/-- With bits ≤ shift + 11, 2^8 plus the ceiling is at most 2,436,593,409 (its value at the
difference 11). -/
theorem gapCeiling_le_of_close {bits shift : ℕ} (close : bits ≤ shift + 11) :
    2 ^ 8 + gapCeiling bits shift ≤ 2436593409 := by
  have power : (2 : ℤ) ^ (bits - shift) ≤ 2048 :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by omega : bits - shift ≤ 11)) (by norm_num)
  unfold gapCeiling
  linarith

/-- With bits ≤ shift + 11, 2^8 plus the ceiling is below 3 · 2^30 (which is below 2^32). -/
theorem gapCeiling_lt_of_close {bits shift : ℕ} (close : bits ≤ shift + 11) :
    2 ^ 8 + gapCeiling bits shift < 3 * 2 ^ 30 :=
  lt_of_le_of_lt (gapCeiling_le_of_close close) (by norm_num)

/-- **At valid settings with MF ≤ KF + 11 a policy with theta and C from 2,436,593,409 on excludes
no output by its scores, whatever the weights and whatever cap is**: under all weights, every output
that has scores and meets clause (c) of `MeetsPolicy` meets it. Limits: see the head of this file;
for the differences 12, 13 and 14 nothing is said. -/
theorem meetsPolicy_of_close_scales (valid : settingsAreValid settings = true)
    (close : settings.finalBits ≤ settings.finalShift + 11) {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
      settings.positions ≤ prompt.length + position →
        modelNextToken settings weights (prompt ++ output.take position) = some output[position])
    (clip : 2436593409 ≤ policy.C) (mean : 2436593409 ≤ policy.theta) :
    MeetsPolicy settings policy weights prompt output :=
  meetsPolicy_of_gapCeiling_le valid scores after
    (le_trans (gapCeiling_le_of_close close) (by exact_mod_cast clip))
    (le_trans (gapCeiling_le_of_close close) (by exact_mod_cast mean))

/-- **At valid settings with MF ≤ KF + 11 some policy with 2^8 ≤ theta < C < 2^32 and cap = 0
excludes no output by its scores, whatever the weights**: under all weights, every output that has
scores and meets clause (c) of `MeetsPolicy` meets it. The policy is (2^32 - 1, 2,436,593,409, 0).
So theta < C and cap = 0 do not by themselves make a policy say something: whether they do depends
on the final norm's exponents. At the settings of the reference scales there is no such policy: none
with theta < C < 2^32 is met under all weights by every output that has scores and meets clause (c)
(`TeethAll.every_output_meets_iff`, Policy/Front/TeethAllChannels.lean). At this policy the
library's port of `policyEmpty` returns 0, "none of these" (`OnBytes.Model.policyEmpty`,
OnBytes/Model/Config.lean, at the exponent 8, by `policyEmpty_eq_zero_iff`,
Johnson/IMR/MeetsPolicyAtPort.lean): an instance, whatever the weights, of that definition's own
caution that a policy at 0 can still let every token through. -/
theorem exists_policy_of_close_scales (valid : settingsAreValid settings = true)
    (close : settings.finalBits ≤ settings.finalShift + 11) :
    ∃ policy : Inst.Model.AcceptancePolicy, policy.C < 2 ^ 32 ∧ policy.theta < policy.C ∧ policy.cap = 0 ∧
      2 ^ 8 ≤ policy.theta ∧
      ∀ (weights : ModelWeights settings) (prompt output : List Token),
        HasScores settings weights prompt output →
        (∀ position (h : position < output.length),
          settings.positions ≤ prompt.length + position →
            modelNextToken settings weights (prompt ++ output.take position) =
              some output[position]) →
        MeetsPolicy settings policy weights prompt output :=
  ⟨⟨4294967295, 2436593409, 0⟩, by norm_num, by norm_num, rfl, by norm_num,
    fun _ _ _ scores after =>
      meetsPolicy_of_close_scales valid close scores after (by norm_num) (le_refl _)⟩

/-- Valid settings stay valid if the final norm's two exponents are replaced by any pair in range.
So there are valid settings with every difference from 0 to 14, given that there are valid settings
at all (`referenceSettings_valid`, VerifiableInference/ModelGuardsAtReference.lean). -/
theorem settingsAreValid_of_final (valid : settingsAreValid settings = true) {bits shift : ℕ}
    (inRange : normInRange bits shift settings.finalEps = true) :
    settingsAreValid { settings with finalBits := bits, finalShift := shift } = true := by
  unfold settingsAreValid settingsInRange at valid
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at valid
  obtain ⟨⟨sizes, -, layers⟩, size⟩ := valid
  show (hasModelSizes settings &&
    (normInRange bits shift settings.finalEps &&
      (List.range 48).all fun layer =>
        layerSettingsInRange (settings.isMixture layer) (settings.perLayer.entry layer) &&
          (settings.perLayer.entry layer).softmaxShift ==
            (settings.perLayer.entry (4 * (layer / 4))).softmaxShift) &&
    settings.perLayer.size == settings.layers) = true
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨sizes, inRange, layers⟩, size⟩

end Policy

#print axioms Policy.NormOutput.reciprocal_mul_succ_le
#print axioms Policy.NormOutput.abs_le_square_add
#print axioms Policy.NormOutput.abs_clamp_le
#print axioms Policy.NormOutput.abs_clamp_roundShift_le
#print axioms Policy.NormOutput.mul_sumOver_le
#print axioms Policy.NormOutput.sumOver_mul_sub_le
#print axioms Policy.NormOutput.sum_le_of_summed
#print axioms Policy.NormOutput.sum_abs_le_of_norm
#print axioms Policy.NormOutput.sum_abs_rmsNorm_out_le
#print axioms Policy.NormOutput.entry_within
#print axioms Policy.NormOutput.product_entry
#print axioms Policy.NormOutput.product_entry_sub_le
#print axioms Policy.NormOutput.trace_logits_entry
#print axioms Policy.NormOutput.logitGap_le_of_differences
#print axioms Policy.NormOutput.final_of_valid
#print axioms Policy.gapCeiling
#print axioms Policy.logitGap_le_gapCeiling
#print axioms Policy.outputCost_le_gapCeiling
#print axioms Policy.meetsPolicy_of_gapCeiling_le
#print axioms Policy.meetsPolicy_iff_of_gapCeiling_le
#print axioms Policy.gapCeiling_le_of_close
#print axioms Policy.gapCeiling_lt_of_close
#print axioms Policy.meetsPolicy_of_close_scales
#print axioms Policy.exists_policy_of_close_scales
#print axioms Policy.settingsAreValid_of_final
