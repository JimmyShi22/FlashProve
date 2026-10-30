-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Allot.lean: pads indexed by numbers, in one pad vector of n entries divided into intervals.
(Words of this library: lean/GLOSSARY.md.)

The blocks take the indices of their pads as maps into the index set of all pads, often from numbers
(a round, a layer). Here the index set is Fin n, and an index is given by a number:
`allot hn k` is the index k, for k < n (beyond n it wraps around, so that the map is total and no
choice is made). `region hn a b` is the set of the indices a, ..., b - 1 (modulo n).
 * `allot_inj`: different numbers below n give different indices;
 * `mem_region`, `region_mono`: a number in the interval gives an index in the region; a larger
   interval gives a larger region; `region_disjoint`: intervals below n that do not overlap give
   disjoint regions.
-/
import Mathlib.Data.Set.Image
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

namespace Blocks

variable {n : ℕ} (hn : 0 < n)

/-- The index k modulo n. -/
def allot (k : ℕ) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

theorem allot_val {k : ℕ} (hk : k < n) : (allot hn k).val = k := Nat.mod_eq_of_lt hk

/-- Different numbers below n give different indices. -/
theorem allot_inj {k k' : ℕ} (hk : k < n) (hk' : k' < n) (h : allot hn k = allot hn k') :
    k = k' := by
  have h1 := congrArg Fin.val h
  rwa [allot_val hn hk, allot_val hn hk'] at h1

/-- The indices a, ..., b - 1 (modulo n). -/
def region (a b : ℕ) : Set (Fin n) := allot hn '' Set.Ico a b

theorem mem_region {a b k : ℕ} (h1 : a ≤ k) (h2 : k < b) : allot hn k ∈ region hn a b :=
  ⟨k, ⟨h1, h2⟩, rfl⟩

theorem region_mono {a b a' b' : ℕ} (h1 : a' ≤ a) (h2 : b ≤ b') : region hn a b ⊆ region hn a' b' :=
  Set.image_mono fun _ hk => ⟨h1.trans hk.1, lt_of_lt_of_le hk.2 h2⟩

/-- Intervals below n that do not overlap give disjoint regions. -/
theorem region_disjoint {a b c d : ℕ} (hbc : b ≤ c) (hd : d ≤ n) :
    Disjoint (region hn a b) (region hn c d) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨k, hk, rfl⟩ ⟨k', hk', h⟩
  have h1 := allot_inj hn (lt_of_lt_of_le hk'.2 hd)
    (lt_of_lt_of_le (lt_of_lt_of_le hk.2 hbc) ((hk'.1.trans hk'.2.le).trans hd)) h
  have h2 := hk.2
  have h3 := hk'.1
  omega

end Blocks
