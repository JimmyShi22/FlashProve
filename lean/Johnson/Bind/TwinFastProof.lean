-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinFastProof.lean: the fast encoder's columns are the plain encoder's: a proof of the
statement `FastIsPlain` (Johnson/Bind/TwinFast.lean), and with it: the committer at the fast encoder
is the committer.

The parts. Johnson/Bind/TwinFastArrays.lean: the transform on arrays computes a polynomial's values
if its factors are the points' powers. Johnson/Bind/TwinFastFactors.lean: they are, in codes of at
most 2^32 positions. Johnson/Bind/TwinFastBytes.lean: words laid as bytes are read back as they were
laid. Here:
   `allOk_spread`: the transform leaves words below p where it found such;
   `getD_startOf`: the array from which a block starts holds the row's coefficients: the tail, the
      plain entries, the pads, each as its residue, then zeros;
   `le_two_pow_span`: the coefficients fit a block;
   `row_symbol`: word i of a row's bytes at the block B is the plain encoder's symbol of that row at
      the position B 2^span + i: both are below p, and read as elements of the field both are the
      polynomial's value at the position's point (`OnBytes.Slice.toF_symF`, `spread_spec`);
   `fastIsPlain`: the statement.
   `commitFastW_is_commitW`: at every shape with a ≤ 32 and l + r ≤ 2^a, over every lawful monad and
      every hash, all files and every table: `commitFastW` is `commitW`.
The same equation at the small stored example's shape and at the full size's, which meet these two
premises, is in Johnson/Bind/TwinFastShapes.lean.
Limits. Equations between two texts of this library. Nothing on what the programs (the C++
implementation that comes with this Lean code) compute.

-/
import Johnson.Bind.TwinFastFactors
import Johnson.Bind.TwinFastBytes
import Johnson.Bind.TwinFastLaws
import Johnson.Bind.TwinRows
import OnBytes.Slice.SimBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open OnBytes (addF subF mulF normF)
open OnBytes.Slice (toF)

/-! ### Sizes -/

theorem size_butterflies (t : UInt64) (off half : Nat) :
    ∀ (n j : Nat) (A : Array UInt64), (butterflies t off half n j A).size = A.size
  | 0, _, _ => rfl
  | n + 1, j, A => by
    show (butterflies t off half n (j + 1) _).size = _
    rw [size_butterflies t off half n (j + 1), Array.size_setIfInBounds, Array.size_setIfInBounds]

theorem size_spread (roots sev : Array UInt64) :
    ∀ (k B off : Nat) (A : Array UInt64), (spread roots sev k B off A).size = A.size
  | 0, _, _, _ => rfl
  | k + 1, B, off, A => by
    show (spread roots sev k (2 * B + 1) (off + 2 ^ k) (spread roots sev k (2 * B) off
      (butterflies (twiddle roots sev k B) off (2 ^ k) (2 ^ k) 0 A))).size = _
    rw [size_spread roots sev k, size_spread roots sev k, size_butterflies]

/-! ### Words below p -/

/-- Every entry is below p. -/
def AllOk (A : Array UInt64) : Prop := ∀ x, Fmt.Fld.two.ok (A.getD x 0) = true

theorem ok_zero : Fmt.Fld.two.ok 0 = true := by decide

theorem ok_addF (a b : UInt64) : Fmt.Fld.two.ok (addF a b) = true := by
  rw [OnBytes.addF_eq]
  exact Fmt.Fld.ok_add _ _ _

theorem ok_subF (a b : UInt64) : Fmt.Fld.two.ok (subF a b) = true := by
  rw [OnBytes.subF_eq]
  exact Fmt.Fld.ok_sub _ _ _

theorem ok_normF (a : UInt64) : Fmt.Fld.two.ok (normF a) = true := by
  have h : (normF a).toNat < Fmt.Fld.two.p := by
    rw [OnBytes.toNat_normF, OnBytes.p_two]
    exact Nat.mod_lt _ (by decide)
  exact decide_eq_true h

theorem allOk_butterflies (t : UInt64) (off half n j : Nat) (A : Array UInt64) (hj : j + n ≤ half)
    (hA : off + 2 * half ≤ A.size) (h : AllOk A) : AllOk (butterflies t off half n j A) := by
  obtain ⟨_, b2, b3, b4⟩ := getD_butterflies t off half n j A hj hA
  intro x
  by_cases h1 : off + j ≤ x ∧ x < off + j + n
  · obtain ⟨i, rfl⟩ : ∃ i, x = off + i := ⟨x - off, by omega⟩
    rw [b2 i (by omega) (by omega)]
    exact ok_addF _ _
  · by_cases h2 : off + half + j ≤ x ∧ x < off + half + j + n
    · obtain ⟨i, rfl⟩ : ∃ i, x = off + half + i := ⟨x - (off + half), by omega⟩
      rw [b3 i (by omega) (by omega)]
      exact ok_subF _ _
    · rw [b4 x fun i g1 g2 => ⟨by omega, by omega⟩]
      exact h x

theorem allOk_spread (roots sev : Array UInt64) :
    ∀ (k B off : Nat) (A : Array UInt64), off + 2 ^ k ≤ A.size → AllOk A →
      AllOk (spread roots sev k B off A)
  | 0, _, _, _, _, h => h
  | k + 1, B, off, A, hA, h => by
    have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [pow_succ]
      ring
    rw [hp] at hA
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    show AllOk (spread roots sev k (2 * B + 1) (off + 2 ^ k) (spread roots sev k (2 * B) off
      (butterflies (twiddle roots sev k B) off (2 ^ k) (2 ^ k) 0 A)))
    refine allOk_spread roots sev k _ _ _ (by rw [size_spread, size_butterflies]; omega) ?_
    refine allOk_spread roots sev k _ _ _ (by rw [size_butterflies]; omega) ?_
    exact allOk_butterflies _ off (2 ^ k) (2 ^ k) 0 A (by omega) (by omega) h

theorem ok_hornerF (z : UInt64) : ∀ cs : List UInt64, Fmt.Fld.two.ok (Fmt.M1.hornerF z cs) = true
  | [] => ok_zero
  | _ :: _ => Fmt.Fld.ok_add _ _ _

theorem ok_symF (C : Fmt.M1.Code) (x : Nat) (m rho : List UInt64) :
    Fmt.Fld.two.ok (Fmt.M1.symF C x m rho) = true := ok_hornerF _ _

/-! ### The coefficients -/

theorem getD_list_map_range (f : Nat → UInt64) (n k : Nat) (h : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  have hl : k < ((List.range n).map f).length := by
    rw [List.length_map, List.length_range]
    exact h
  rw [List.getD_eq_getElem _ _ hl, List.getElem_map, List.getElem_range]

section
variable (S : Shape) (T : Table) (b : Nat)

theorem ok_coefficient (j : Nat) : Fmt.Fld.two.ok (coefficient S T b j) = true := by
  unfold coefficient
  split
  · exact ok_normF _
  · split
    · exact ok_normF _
    · split
      · exact ok_normF _
      · exact ok_zero

theorem coefficient_beyond (j : Nat) (h : S.r + S.l ≤ j) : coefficient S T b j = 0 := by
  unfold coefficient Shape.plain
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem toF_coefficient_tail (q : Nat) (h : q < S.r) :
    toF (coefficient S T b q) = toF ((tailOf S T b).getD q 0) := by
  unfold coefficient tailOf
  rw [if_pos h, OnBytes.Slice.toF_normF, getD_list_map_range _ _ _ h]

theorem toF_coefficient_message (j : Nat) (h : j < S.l) :
    toF (coefficient S T b (S.r + j)) = toF ((message S T b).getD j 0) := by
  unfold coefficient message
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  by_cases hp : j < S.plain
  · rw [if_pos hp, OnBytes.Slice.toF_normF,
      List.getD_append _ _ _ _ (by rw [List.length_map, List.length_range]; exact hp),
      getD_list_map_range _ _ _ hp]
  · have hq : j - S.plain < S.pads := by
      unfold Shape.plain Shape.pads at *
      omega
    rw [if_neg hp, if_pos h, OnBytes.Slice.toF_normF,
      List.getD_append_right _ _ _ _ (by rw [List.length_map, List.length_range]; omega),
      List.length_map, List.length_range, getD_list_map_range _ _ _ hq]

/-- The array from which each block of the row b starts. -/
def startOf : Array UInt64 :=
  unpack (2 ^ S.span) (packFrom (coefficient S T b) (S.r + S.l) 0 ByteArray.empty)

theorem size_startOf : (startOf S T b).size = 2 ^ S.span := by
  unfold startOf unpack
  rw [Array.size_map, Array.size_range]

theorem getD_startOf (j : Nat) (h : j < 2 ^ S.span) :
    (startOf S T b).getD j 0 = coefficient S T b j := by
  unfold startOf unpack
  rw [getD_map_range _ _ _ h, wordAt_packFrom]
  by_cases hj : j < S.r + S.l
  · rw [if_pos hj]
  · rw [if_neg hj, coefficient_beyond S T b j (by omega)]

theorem allOk_startOf : AllOk (startOf S T b) := by
  intro x
  by_cases h : x < 2 ^ S.span
  · rw [getD_startOf S T b x h]
    exact ok_coefficient S T b x
  · rw [Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_none (by rw [size_startOf]; omega)]
    exact ok_zero

end

/-- The coefficients fit a block. -/
theorem le_two_pow_span (S : Shape) (h : S.l + S.r ≤ 2 ^ S.a) : S.r + S.l ≤ 2 ^ S.span := by
  unfold Shape.span
  by_cases h1 : S.l + S.r ≤ 1
  · rw [if_pos h1, Nat.min_eq_right (Nat.zero_le _), pow_zero]
    omega
  · rw [if_neg h1]
    have h2 : S.l + S.r - 1 < 2 ^ (Nat.log2 (S.l + S.r - 1) + 1) := Nat.lt_log2_self
    rcases Nat.le_total S.a (Nat.log2 (S.l + S.r - 1) + 1) with h3 | h3
    · rw [Nat.min_eq_left h3]
      omega
    · rw [Nat.min_eq_right h3]
      omega

/-! ### A row's symbol -/

/-- The polynomial with the row's coefficients, at any point, is the sum that the plain encoder's
symbol is read as. -/
theorem sum_coefficients (S : Shape) (T : Table) (b : Nat) (hS : S.l + S.r ≤ 2 ^ S.a)
    (z : Cb.Gl.F) :
    ∑ j ∈ Finset.range (2 ^ S.span), toF ((startOf S T b).getD j 0) * z ^ j =
      (∑ q ∈ Finset.range S.r, z ^ q * toF ((tailOf S T b).getD q 0)) +
        ∑ j ∈ Finset.range S.l, z ^ (S.r + j) * toF ((message S T b).getD j 0) := by
  have e1 : ∑ j ∈ Finset.range (2 ^ S.span), toF ((startOf S T b).getD j 0) * z ^ j =
      ∑ j ∈ Finset.range (2 ^ S.span), toF (coefficient S T b j) * z ^ j :=
    Finset.sum_congr rfl fun j hj => by rw [getD_startOf S T b j (Finset.mem_range.1 hj)]
  obtain ⟨d, hd⟩ : ∃ d, 2 ^ S.span = S.r + S.l + d :=
    ⟨2 ^ S.span - (S.r + S.l), by have := le_two_pow_span S hS; omega⟩
  have e3 : ∑ j ∈ Finset.range d, toF (coefficient S T b (S.r + S.l + j)) * z ^ (S.r + S.l + j) =
      0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [coefficient_beyond S T b _ (by omega), OnBytes.Slice.toF_zero, zero_mul]
  rw [e1, hd, Finset.sum_range_add, Finset.sum_range_add, e3, add_zero]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun q hq => by
      rw [toF_coefficient_tail S T b q (Finset.mem_range.1 hq), mul_comm]
  · exact Finset.sum_congr rfl fun j hj => by
      rw [toF_coefficient_message S T b j (Finset.mem_range.1 hj), mul_comm]

/-- **Word i of a row's bytes at the block B is the plain encoder's symbol.** -/
theorem row_symbol (S : Shape) (T : Table) (ha : S.a ≤ 32) (hS : S.l + S.r ≤ 2 ^ S.a)
    (b B i : Nat) (hB : B < 2 ^ (S.a - S.span)) (hi : i < 2 ^ S.span) :
    Fmt.wordAt (blockRow (prepare S T) S.span B
        (packFrom (coefficient S T b) (S.r + S.l) 0 ByteArray.empty)) (8 * i) =
      Fmt.M1.symF S.code (B * 2 ^ S.span + i) (message S T b) (tailOf S T b) := by
  have hBa : (B + 1) * 2 ^ S.span ≤ 2 ^ S.a := by
    have h1 : (B + 1) * 2 ^ S.span ≤ 2 ^ (S.a - S.span) * 2 ^ S.span := Nat.mul_le_mul_right _ hB
    rwa [← Nat.pow_add, Nat.sub_add_cancel (span_le S)] at h1
  obtain ⟨_, s2, _⟩ := spread_spec (fun x => toF (Fmt.M1.point S.a x)) (rootsTable (S.a - 1))
    (sevens S.a) S.a (factors_point S.a ha) S.span B 0 (startOf S T b)
    (by rw [size_startOf]; omega) hBa
  have hsz : i < (spread (rootsTable (S.a - 1)) (sevens S.a) S.span B 0 (startOf S T b)).size := by
    rw [size_spread, size_startOf]
    exact hi
  show Fmt.wordAt ((spread (rootsTable (S.a - 1)) (sevens S.a) S.span B 0
    (startOf S T b)).foldl pushWord ByteArray.empty) (8 * i) = _
  rw [wordAt_foldl _ _ hsz]
  refine OnBytes.Slice.toF_inj _ _
    (allOk_spread _ _ _ _ _ _ (by rw [size_startOf]; omega) (allOk_startOf S T b) i)
    (ok_symF _ _ _ _) ?_
  have h2 := s2 i hi
  simp only [Nat.zero_add] at h2
  rw [h2, OnBytes.Slice.toF_symF]
  exact sum_coefficients S T b hS _

/-! ### The statement -/

/-- **The fast encoder's columns are the plain encoder's.** -/
theorem fastIsPlain : FastIsPlain := by
  intro S T ha hS B i hB hi
  have hr : (prepare S T).rows = (Array.range S.rows).map fun b =>
      packFrom (coefficient S T b) (S.r + S.l) 0 ByteArray.empty := rfl
  rw [columnOf_laid]
  show (((prepare S T).rows.map (blockRow (prepare S T) S.span B)).toList.map fun row =>
    Fmt.wordAt row (8 * i)) = _
  rw [hr, Array.toList_map, Array.toList_map, Array.toList_range, List.map_map, List.map_map]
  exact List.map_congr_left fun b _ => row_symbol S T ha hS b B i hB hi

/-- **The committer at the fast encoder is the committer**, at every shape with at most 2^32
positions whose polynomials are no longer than its codewords. -/
theorem commitFastW_is_commitW {m : Type → Type} [Monad m] [LawfulMonad m]
    (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray) (S : Shape) (ha : S.a ≤ 32)
    (hS : S.l + S.r ≤ 2 ^ S.a) (files : List ByteArray) (T : Table) :
    commitFastW h S files T = commitW h S files T :=
  commitFastW_eq h fastIsPlain S ha hS files T

end Bind.Twin

#print axioms Bind.Twin.size_butterflies
#print axioms Bind.Twin.size_spread
#print axioms Bind.Twin.ok_zero
#print axioms Bind.Twin.ok_addF
#print axioms Bind.Twin.ok_subF
#print axioms Bind.Twin.ok_normF
#print axioms Bind.Twin.allOk_butterflies
#print axioms Bind.Twin.allOk_spread
#print axioms Bind.Twin.ok_hornerF
#print axioms Bind.Twin.ok_symF
#print axioms Bind.Twin.getD_list_map_range
#print axioms Bind.Twin.ok_coefficient
#print axioms Bind.Twin.coefficient_beyond
#print axioms Bind.Twin.toF_coefficient_tail
#print axioms Bind.Twin.toF_coefficient_message
#print axioms Bind.Twin.size_startOf
#print axioms Bind.Twin.getD_startOf
#print axioms Bind.Twin.allOk_startOf
#print axioms Bind.Twin.le_two_pow_span
#print axioms Bind.Twin.sum_coefficients
#print axioms Bind.Twin.row_symbol
#print axioms Bind.Twin.fastIsPlain
#print axioms Bind.Twin.commitFastW_is_commitW
