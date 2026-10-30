-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/BlkPlanes.lean: a vector on a lookup's multiplicities, laid on the prover's message.

The prover of a key file's first chain sends how often each row of a range table is met, in bits:
bit j of the count of row t is the entry j + 2 ^ mu t of the lookup's vector of multiplicities, and
the bits number j of all rows are plane j (OnBytes/Iop/Lkp.lean). The real planes lie in the main
table of one oracle message, in aligned blocks of planes (OnBytes/Key/Ranges.lean: `Wf.Block`,
`Wf.layout`). `Wf.planesAt` (OnBytes/Iop/Wf.lean) adds a vector on the multiplicities to a row: for
each block of the lookup one structured vector on the table.

This file says what these structured vectors add up to, under any reading of the program's elements
and for any table T, given by the index of an entry. The bit at (row t, plane j) is defined by what
the vectors read (`bitAt`): the sum, over the blocks that hold plane j, of the table's entry at the
index that the block's vector picks (`blockIdx`); 0 if no block holds the plane. The law
(`blocks_value`): for a vector v of product form on mu + d variables, the sum over the table's
indices of the vectors' entries times T is the sum over all planes j and rows t of v's entry at j +
2 ^ mu t times the bit at (t, j).

What is asked of each block by itself (`BlockFits`): its planes are an aligned block below 2 ^ mu,
it has as many index bits as its planes and the d row variables need, and these are at most the
index bits of a place in a row of the table. Nothing is asked of the blocks together: not that they
hold each real plane once, not that they lie apart in the table.

Main definitions: `blockIdx`, `bitAt`, `BlockFits`, `blockTensor`.
Main theorems.
 `sum_insertChoice`   a sum under a vector with choice variables put in.
 `block_value`        one block's vector.
 `sum_block_planes`   one block's sum, over all planes and rows.
 `blocks_value`       all blocks' vectors.

Not claimed. That the blocks of `Wf.layout` meet `BlockFits`. Nothing on a row's other summands.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkSetBits
import OnBytes.Iop.Wf
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace OnBytes.Slice.Planes
open OnBytes.Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## A sum under a vector with choice variables put in -/

/-- An index below 2 ^ (n + count) without count of its bits is below 2 ^ n. -/
theorem unshift_lt (pos count n J : ℕ) (hp : pos ≤ n) (hJ : J < 2 ^ (n + count)) :
    unshift pos count J < 2 ^ n := by
  unfold unshift
  have h1 : J / 2 ^ (pos + count) < 2 ^ (n - pos) := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, show pos + count + (n - pos) = n + count by omega]
    exact hJ
  have h2 := Nat.mod_lt J (Nat.two_pow_pos pos)
  have h3 : 2 ^ n = 2 ^ pos * 2 ^ (n - pos) := by rw [← pow_add, Nat.add_sub_cancel' hp]
  rw [h3]
  calc J % 2 ^ pos + 2 ^ pos * (J / 2 ^ (pos + count))
      < 2 ^ pos + 2 ^ pos * (J / 2 ^ (pos + count)) := by omega
    _ = 2 ^ pos * (J / 2 ^ (pos + count) + 1) := by ring
    _ ≤ 2 ^ pos * 2 ^ (n - pos) := Nat.mul_le_mul_left _ h1

/-- An index below 2 ^ n with count bits put in is below 2 ^ (n + count). -/
theorem shiftIn_lt (pos count value n e : ℕ) (hp : pos ≤ n) (he : e < 2 ^ n) :
    shiftIn pos count value e < 2 ^ (n + count) := by
  rw [shiftIn_form]
  have h1 : e / 2 ^ pos < 2 ^ (n - pos) := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_sub_cancel' hp]
    exact he
  have h2 := Nat.mod_lt e (Nat.two_pow_pos pos)
  have h3 := Nat.mod_lt value (Nat.two_pow_pos count)
  have h4 : 2 ^ (n + count) = 2 ^ pos * (2 ^ (n - pos) * 2 ^ count) := by
    rw [← pow_add, ← pow_add, show pos + (n - pos + count) = n + count by omega]
  rw [h4]
  have h5 : value % 2 ^ count + e / 2 ^ pos * 2 ^ count + 1 ≤ 2 ^ (n - pos) * 2 ^ count := by
    calc value % 2 ^ count + e / 2 ^ pos * 2 ^ count + 1
        ≤ 2 ^ count + e / 2 ^ pos * 2 ^ count := by omega
      _ = (e / 2 ^ pos + 1) * 2 ^ count := by ring
      _ ≤ 2 ^ (n - pos) * 2 ^ count := Nat.mul_le_mul_right _ h1
  calc e % 2 ^ pos + 2 ^ pos * (value % 2 ^ count + e / 2 ^ pos * 2 ^ count)
      < 2 ^ pos + 2 ^ pos * (value % 2 ^ count + e / 2 ^ pos * 2 ^ count) := by omega
    _ = 2 ^ pos * (value % 2 ^ count + e / 2 ^ pos * 2 ^ count + 1) := by ring
    _ ≤ 2 ^ pos * (2 ^ (n - pos) * 2 ^ count) := Nat.mul_le_mul_left _ h5

/-- A sum under a vector with choice variables put in is the sum under the vector, at the
indices with the bits put in. -/
theorem sum_insertChoice (v : Tensor) (pos count value n : ℕ) (hn : v.vars = n) (hp : pos ≤ n)
    (T : ℕ → K) :
    ∑ J ∈ Finset.range (2 ^ (n + count)),
        ρ.val ((v.insertChoice pos count value).entry J) * T J =
      ∑ e ∈ Finset.range (2 ^ n), ρ.val (v.entry e) * T (shiftIn pos count value e) := by
  have e1 : ∀ J, ρ.val ((v.insertChoice pos count value).entry J) * T J =
      if J / 2 ^ pos % 2 ^ count = value % 2 ^ count then
        ρ.val (v.entry (unshift pos count J)) * T J else 0 := by
    intro J
    rw [Tensor.entry_insertChoice ρ v pos count value J (by rw [hn]; exact hp)]
    by_cases h : J / 2 ^ pos % 2 ^ count = value % 2 ^ count
    · rw [if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun J _ => e1 J, ← Finset.sum_filter]
  refine Finset.sum_nbij' (unshift pos count) (shiftIn pos count value) ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    rw [Finset.mem_filter, Finset.mem_range] at hJ
    exact Finset.mem_range.2 (unshift_lt pos count n J hp hJ.1)
  · intro e he
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨shiftIn_lt pos count value n e hp (Finset.mem_range.1 he),
      ((shiftIn_eq_iff pos count value e _).1 rfl).1⟩
  · intro J hJ
    rw [Finset.mem_filter] at hJ
    exact (shiftIn_eq_iff pos count value _ J).2 ⟨hJ.2, rfl⟩
  · intro e _
    exact unshift_shiftIn pos count value e
  · intro J hJ
    rw [Finset.mem_filter] at hJ
    rw [(shiftIn_eq_iff pos count value _ J).2 ⟨hJ.2, rfl⟩]

/-! ## One block -/

/-- The index of the table's entry that a block's vector picks for the block's entry e. rb: the
number of the table's row bits, which are the low bits of an index. logEll: the number of the index
bits of a place in a row. -/
def blockIdx (rb logEll : ℕ) (b : Wf.Block) (e : ℕ) : ℕ :=
  shiftIn 0 rb b.row (shiftIn b.bits (logEll - b.bits) (b.firstPlace / 2 ^ b.bits) e)

/-- The structured vector that `Wf.planesAt` adds for one block. -/
def blockTensor (v : Tensor) (mu rb logEll : ℕ) (b : Wf.Block) : Tensor :=
  ((Lkp.onBlock v mu (b.first, b.logPlanes)).insertChoice b.bits (logEll - b.bits)
    (b.firstPlace / 2 ^ b.bits)).insertChoice 0 rb b.row

/-- What is asked of a block by itself. -/
structure BlockFits (mu d logEll : ℕ) (b : Wf.Block) : Prop where
  lb : b.logPlanes ≤ mu
  aligned : b.first % 2 ^ b.logPlanes = 0
  inside : b.first + 2 ^ b.logPlanes ≤ 2 ^ mu
  bits : b.bits = b.logPlanes + d
  room : b.bits ≤ logEll

/-- Choice variables that are put in add to the number of variables. -/
theorem vars_insertChoice (v : Tensor) (pos count value : ℕ) (h : pos ≤ v.vars) :
    (v.insertChoice pos count value).vars = v.vars + count := by
  unfold Tensor.vars at h ⊢
  unfold Tensor.insertChoice
  show (v.pairs.take pos ++ choicePairs count value ++ v.pairs.drop pos).length = _
  rw [List.length_append, List.length_append, List.length_take, List.length_drop,
    choicePairs_length]
  omega

/-- A sum over the numbers below a b, by low and high part. -/
theorem sum_range_mul' (F : ℕ → K) (a : ℕ) : ∀ b : ℕ,
    ∑ j ∈ Finset.range (a * b), F j =
      ∑ p ∈ Finset.range b, ∑ c ∈ Finset.range a, F (c + a * p)
  | 0 => by simp
  | b + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul' F a b, Finset.sum_range_succ]
    refine congrArg _ (Finset.sum_congr rfl fun c _ => ?_)
    rw [Nat.add_comm]

/-- One block's vector: the sum over the table's indices of its entries times the table is the
sum, over the rows t and the block's planes j', of the vector's entry at the plane first + j' and
the row t, times the table's entry that the block's vector picks. -/
theorem block_value (v : Tensor) (mu d rb logEll : ℕ) (b : Wf.Block) (hv : v.denseVars = [])
    (hl : v.pairs.length = mu + d) (hb : BlockFits mu d logEll b) (T : ℕ → K) :
    ∑ J ∈ Finset.range (2 ^ (logEll + rb)),
        ρ.val ((blockTensor v mu rb logEll b).entry J) * T J =
      ∑ t ∈ Finset.range (2 ^ d), ∑ j' ∈ Finset.range (2 ^ b.logPlanes),
        ρ.val (v.entry (b.first + j' + 2 ^ mu * t)) *
          T (blockIdx rb logEll b (j' + 2 ^ b.logPlanes * t)) := by
  have hv1 : (Lkp.onBlock v mu (b.first, b.logPlanes)).vars = b.bits := by
    unfold Lkp.onBlock
    rw [vars_setBits v _ _ _ hb.lb (by omega), hl, hb.bits]
    have := hb.lb
    omega
  have hv2 : ((Lkp.onBlock v mu (b.first, b.logPlanes)).insertChoice b.bits (logEll - b.bits)
      (b.firstPlace / 2 ^ b.bits)).vars = logEll := by
    rw [vars_insertChoice _ _ _ _ (le_of_eq hv1.symm), hv1, Nat.add_sub_cancel' hb.room]
  unfold blockTensor
  rw [sum_insertChoice ρ _ 0 rb b.row logEll hv2 (Nat.zero_le _)]
  have h3 := sum_insertChoice ρ (Lkp.onBlock v mu (b.first, b.logPlanes)) b.bits
    (logEll - b.bits) (b.firstPlace / 2 ^ b.bits) b.bits hv1 (le_refl _)
    (fun J => T (shiftIn 0 rb b.row J))
  rw [Nat.add_sub_cancel' hb.room] at h3
  rw [h3, hb.bits, pow_add, sum_range_mul']
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun j' hj => ?_
  have hf : b.first < 2 ^ mu := by
    have := hb.inside
    have := Nat.two_pow_pos b.logPlanes
    omega
  rw [entry_onBlock ρ v mu b.first b.logPlanes j' t hv hb.lb (by omega) hb.aligned hf
    (Finset.mem_range.1 hj) (by rw [hl, Nat.add_sub_cancel_left]; exact Finset.mem_range.1 ht)]
  unfold blockIdx
  rw [hb.bits, pow_add]

/-- One block's sum, over all planes and rows. -/
theorem sum_block_planes (mu d first lb : ℕ) (h : first + 2 ^ lb ≤ 2 ^ mu) (V : ℕ → K)
    (X : ℕ → K) :
    ∑ t ∈ Finset.range (2 ^ d), ∑ j' ∈ Finset.range (2 ^ lb),
        V (first + j' + 2 ^ mu * t) * X (j' + 2 ^ lb * t) =
      ∑ j ∈ Finset.range (2 ^ mu), ∑ t ∈ Finset.range (2 ^ d), V (j + 2 ^ mu * t) *
        (if first ≤ j ∧ j < first + 2 ^ lb then X (j - first + 2 ^ lb * t) else 0) := by
  rw [Finset.sum_comm]
  have hsub : Finset.Ico first (first + 2 ^ lb) ⊆ Finset.range (2 ^ mu) := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_Ico.1 hx).2 h)
  rw [← Finset.sum_subset hsub fun x _ hx => Finset.sum_eq_zero fun t _ => by
    rw [if_neg fun hc => hx (Finset.mem_Ico.2 hc), mul_zero]]
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun j' hj => Finset.sum_congr rfl fun t _ => ?_
  have hj' := Finset.mem_range.1 hj
  rw [if_pos ⟨Nat.le_add_right _ _, by omega⟩, Nat.add_sub_cancel_left]

/-! ## All blocks -/

/-- The bit at (row t, plane j), as the blocks' vectors read it off the table T: the sum, over
the blocks that hold plane j, of the entry that the block's vector picks; 0 if no block holds the
plane. -/
def bitAt (rb logEll : ℕ) (bs : List Wf.Block) (T : ℕ → K) (t j : ℕ) : K :=
  (bs.map fun b =>
    if b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes then
      T (blockIdx rb logEll b (j - b.first + 2 ^ b.logPlanes * t)) else 0).sum

/-- All blocks' vectors: the sum over the table's indices of their entries times the table is
the sum over all planes and rows of the vector's entry times the bit. -/
theorem blocks_value (v : Tensor) (mu d rb logEll : ℕ) (hv : v.denseVars = [])
    (hl : v.pairs.length = mu + d) (T : ℕ → K) : ∀ bs : List Wf.Block,
    (∀ b ∈ bs, BlockFits mu d logEll b) →
    ∑ J ∈ Finset.range (2 ^ (logEll + rb)),
        (bs.map fun b => ρ.val ((blockTensor v mu rb logEll b).entry J)).sum * T J =
      ∑ j ∈ Finset.range (2 ^ mu), ∑ t ∈ Finset.range (2 ^ d),
        ρ.val (v.entry (j + 2 ^ mu * t)) * bitAt rb logEll bs T t j
  | [], _ => by simp [bitAt]
  | b :: bs, h => by
    have ih := blocks_value v mu d rb logEll hv hl T bs fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hb := h b List.mem_cons_self
    have one := block_value ρ v mu d rb logEll b hv hl hb T
    rw [sum_block_planes mu d b.first b.logPlanes hb.inside (fun x => ρ.val (v.entry x))
      (fun e => T (blockIdx rb logEll b e))] at one
    simp only [List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, bitAt, mul_add]
    rw [one]
    exact congrArg _ ih

end OnBytes.Slice.Planes
