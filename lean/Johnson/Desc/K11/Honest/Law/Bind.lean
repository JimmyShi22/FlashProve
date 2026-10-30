-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K11/Honest/Law/Bind.lean: BINDING IS THE EQUALITY-WEIGHTED SUM: a table of 2 ^ k
entries with all its bits bound at k challenges (`bindAll`, Johnson/Desc/K11/Honest/Summand.lean)
reads as the sum over its entries of the library's equality weight of the entry's number at the
challenges (`Blocks.eqN`, Blocks/Basic.lean) times the entry. A lemma on lists, with its helps and
proofs. No frame, no verifier's text.

The chief names:
  `bindTop_getD`        an entry of a table with its highest bit bound
  `eqN_succ_top`        the equality weight, its first coordinate split off: the top bit's
  `eqN_above`           the weight of m coordinates does not see bit m
  `bindAll_head_read`   the lemma

The first challenge goes with the highest bit: as in `Blocks.eqN`, and as in the point that spells a
column (`bitsOf`, Johnson/Road/FormsKeysWm.lean).

Limits. The table's length is a premise. Nothing on any property.

-/
import Johnson.Desc.K11.Honest.Law.Tables
import Johnson.Road.FormsKeysMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Honest
open OnBytes (E addE subE mulE zeroE)
open OnBytes.Model (Reading)
open OnBytes.Road (pt)

/-- An entry of a table with its highest bit bound. h: half the table's length. -/
theorem bindTop_getD (r : E) (t : List E) (h j : Nat) (ht : t.length = 2 * h) (hj : j < h) :
    (bindTop r t).getD j zeroE =
      addE (t.getD j zeroE) (mulE r (subE (t.getD (h + j) zeroE) (t.getD j zeroE))) := by
  have hh : t.length / 2 = h := by omega
  have h1 : j < t.length := by omega
  have h2 : h + j < t.length := by omega
  have hl : j < (bindTop r t).length := by
    rw [bindTop_length]
    omega
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  simp only [bindTop, hh, List.getElem_map, List.getElem_zip, List.getElem_take,
    List.getElem_drop]

/-- A list's member, read off the list as an array. -/
theorem toArray_getD_zero (l : List E) (j : Nat) : l.toArray.getD j zeroE = l.getD j zeroE := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

section Field
variable {K : Type} [Field K] (ρ : Reading K)

/-- The first coordinate of a point that is a list. -/
theorem pt_cons_zero (r : E) (rs : List E) : pt ρ (r :: rs).toArray 0 = ρ.val r := by
  unfold pt
  rw [toArray_getD_zero, List.getD_cons_zero]

/-- Its later coordinates. -/
theorem pt_cons_succ (r : E) (rs : List E) (j : Nat) :
    pt ρ (r :: rs).toArray (j + 1) = pt ρ rs.toArray j := by
  unfold pt
  rw [toArray_getD_zero, toArray_getD_zero, List.getD_cons_succ]

/-- The equality weight, its first coordinate split off: it goes with the top bit. -/
theorem eqN_succ_top (m : Nat) (a : Nat → K) (z : Nat) :
    Blocks.eqN (m + 1) 0 a z =
      (if z.testBit m then a 0 else 1 - a 0) * Blocks.eqN m 0 (fun t => a (t + 1)) z := by
  unfold Blocks.eqN
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  have e : m + 1 - 1 - (t + 1) = m - 1 - t := by omega
  rw [e]
  simp only [Nat.zero_add]

/-- The weight of m coordinates does not see bit m. -/
theorem eqN_above (m : Nat) (a : Nat → K) (C : Nat) :
    Blocks.eqN m 0 a (2 ^ m + C) = Blocks.eqN m 0 a C := by
  unfold Blocks.eqN
  refine Finset.prod_congr rfl fun t ht => ?_
  have hlt : m - 1 - t < m := by
    have := Finset.mem_range.1 ht
    omega
  rw [Nat.testBit_two_pow_add_gt hlt]

/-- **Binding is the equality-weighted sum.** A table with 2 ^ k entries, all its k bits bound at
the challenges rs, the first of rs at the highest bit: its one entry reads as the sum over the
numbers C below 2 ^ k of the library's equality weight of C at rs times entry C of the table. -/
theorem bindAll_head_read : ∀ (rs t : List E), t.length = 2 ^ rs.length →
    ρ.val ((bindAll rs t).headD zeroE) =
      ∑ C ∈ Finset.range (2 ^ rs.length),
        Blocks.eqN rs.length 0 (pt ρ rs.toArray) C * ρ.val (t.getD C zeroE)
  | [], t, h => by
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 (by simpa using h)
    simp [bindAll, Blocks.eqN]
  | r :: rs, t, h => by
    have hm : t.length = 2 * 2 ^ rs.length := by
      rw [h, List.length_cons, pow_succ]
      omega
    have hl : (bindTop r t).length = 2 ^ rs.length := by
      rw [bindTop_length, hm]
      omega
    have e0 : bindAll (r :: rs) t = bindAll rs (bindTop r t) := rfl
    rw [e0, bindAll_head_read rs (bindTop r t) hl, List.length_cons, pow_succ, Nat.mul_two,
      Finset.sum_range_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hC' := Finset.mem_range.1 hC
    have b0 : C.testBit rs.length = false := Nat.testBit_lt_two_pow hC'
    have b1 : (2 ^ rs.length + C).testBit rs.length = true := by
      rw [Nat.testBit_two_pow_add_eq, b0]
      rfl
    have ha : (fun j => pt ρ (r :: rs).toArray (j + 1)) = pt ρ rs.toArray :=
      funext fun j => pt_cons_succ ρ r rs j
    rw [bindTop_getD r t _ C hm hC', eqN_succ_top, eqN_succ_top, b0, b1, ha, eqN_above,
      pt_cons_zero]
    simp only [ρ.add, ρ.mul, ρ.sub, if_true, Bool.false_eq_true, if_false]
    ring

end Field

end Johnson.Desc.First.ForkMerge.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Honest.bindTop_getD
#print axioms Johnson.Desc.First.ForkMerge.Honest.toArray_getD_zero
#print axioms Johnson.Desc.First.ForkMerge.Honest.pt_cons_zero
#print axioms Johnson.Desc.First.ForkMerge.Honest.pt_cons_succ
#print axioms Johnson.Desc.First.ForkMerge.Honest.eqN_succ_top
#print axioms Johnson.Desc.First.ForkMerge.Honest.eqN_above
#print axioms Johnson.Desc.First.ForkMerge.Honest.bindAll_head_read
