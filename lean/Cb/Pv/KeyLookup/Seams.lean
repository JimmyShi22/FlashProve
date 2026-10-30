-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Seams.lean: where two joints of Cb/Pv/KeyLookup/Letters.lean say the same, and the
steps without rounds between
stretches.

It imports Cb/Pv/KeyLookup/Letters.lean alone.

States, for every data A, state x and entries μ:
  `parts_zero`    Parts 0 ⇔ Tied              `keys_zero`  Keys 0 ⇔ Joined         `keys_all`  Keys
                  m ⇔ Table 0
  `roots_endParts` under 1 ≤ m: Roots at the state in which the claim still under way is written
      down as the last part's
                   (`endParts`) ⇔ Parts (m - 1)
  `tied_endTie`   under 1 ≤ pl: the like for the tie's claim under way and the last plane (`endTie`)
  `numRow_holds`  the row on the counts holds ⇔ Num
  `done_rd`       Done at the read-out ⇔ Bitten.
No premise but the two on numbers that are named. Nothing on any block.

-/
import Cb.Pv.KeyLookup.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.Lkp Finset

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (x : A.XS) (μ : A.J → E)

theorem parts_zero : A.Parts x μ 0 ↔ A.Tied x μ :=
  ⟨fun ⟨h1, h2, h3, _⟩ => ⟨h1, h3, h2⟩,
    fun ⟨h1, h3, h2⟩ => ⟨h1, h2, h3, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩

theorem keys_zero : A.Keys x μ 0 ↔ A.Joined x μ :=
  ⟨fun ⟨h1, h2, _, h4⟩ => ⟨h1, fun i hi => h4 i hi (Nat.zero_le i), h2⟩,
    fun ⟨h1, h4, h2⟩ => ⟨h1, h2, fun i hi => absurd hi (Nat.not_lt_zero i), fun i hi _ => h4 i hi⟩⟩

theorem keys_all : A.Keys x μ A.m ↔ A.Table x μ 0 :=
  ⟨fun ⟨h1, h2, h3, _⟩ => ⟨h1, h3, h2⟩,
    fun ⟨h1, h3, h2⟩ => ⟨h1, h2, h3, fun _ hi hm => absurd hi (Nat.not_lt.2 hm)⟩⟩

/-- the product of the roots from the last part on is the last part's root -/
theorem rest_last (st : A.St) (al : E) (h : 1 ≤ A.m) :
    A.rest st μ al (A.m - 1) = A.root st μ al (A.m - 1) := by
  unfold rest
  obtain ⟨k, hk⟩ : ∃ k, A.m = k + 1 := ⟨A.m - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.Ico_succ_singleton, Finset.prod_singleton]

/-- the planes' powers from the last live plane on are that plane's root -/
theorem pow_last (st : A.St) (al : E) (h : 1 ≤ A.pl) :
    A.pow st μ al (A.pl - 1) = A.plane st μ al (A.pl - 1) := by
  unfold pow
  obtain ⟨k, hk⟩ : ∃ k, A.pl = k + 1 := ⟨A.pl - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel, Nat.Ico_succ_singleton, Finset.prod_singleton, Nat.sub_self, pow_zero,
    pow_one]

/-- A step without rounds: the claim on what is still together is the last part's. -/
def endParts : A.XS := { x with roots := fun i => if i = A.m - 1 then x.all else x.roots i }

theorem roots_endParts (h : 1 ≤ A.m) : A.Roots (A.endParts x) μ ↔ A.Parts x μ (A.m - 1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_, fun i hi => ?_⟩
    · have := h3 (A.m - 1) (by omega)
      rw [A.rest_last μ x.st x.al h]
      simpa [endParts] using this
    · have := h3 i (by omega)
      have hne : i ≠ A.m - 1 := by omega
      simpa [endParts, hne] using this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun i hi => ?_⟩
    by_cases hi' : i = A.m - 1
    · subst hi'
      rw [A.rest_last μ x.st x.al h] at h3
      simpa [endParts] using h3
    · have := h4 i (by omega)
      simpa [endParts, hi'] using this

/-- A step without rounds: the tie's claim under way is the last live plane's. -/
def endTie : A.XS := { x with planes := fun j => if j = A.pl - 1 then x.run else x.planes j }

theorem tied_endTie (h : 1 ≤ A.pl) : A.Tied (A.endTie x) μ ↔ A.Tie x μ (A.pl - 1) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_, fun j hj => ?_⟩
    · have := h3 (A.pl - 1) (by omega)
      rw [A.pow_last μ x.st x.al h]
      simpa [endTie] using this
    · have := h3 j (by omega)
      have hne : j ≠ A.pl - 1 := by omega
      simpa [endTie, hne] using this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, fun j hj => ?_⟩
    by_cases hj' : j = A.pl - 1
    · subst hj'
      rw [A.pow_last μ x.st x.al h] at h3
      simpa [endTie] using h3
    · have := h4 j (by omega)
      simpa [endTie, hj'] using this

theorem numRow_holds : A.numRow.Holds μ ↔ A.Num μ := by
  have e : ∑ i, A.numRow.cf i * μ i =
      ∑ u ∈ range (2 ^ A.d), ∑ j ∈ range A.pl, (2 : E) ^ j * A.bit μ u j := by
    unfold numRow
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, bit,
      Finset.mem_range.1 hj]
  unfold Row.Holds Num
  rw [e]
  rfl

theorem done_rd : A.Done μ (A.rd x) ↔ A.Bitten x μ := by
  have r : RowsHold (x.rows ++ [A.numRow]) μ ↔ RowsHold x.rows μ ∧ A.Num μ := by
    rw [← A.numRow_holds μ]
    unfold RowsHold
    constructor
    · intro h
      exact ⟨fun a ha => h a (List.mem_append_left _ ha),
        h _ (List.mem_append_right _ (List.mem_singleton.2 rfl))⟩
    · rintro ⟨h1, h2⟩ a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact h1 a ha
      · rw [List.mem_singleton.1 ha]
        exact h2
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(r.1 h2).2, (r.1 h2).1⟩, fun i hi => h1 ⟨i, hi⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨fun i => h3 i i.2, r.2 ⟨h2, h1⟩⟩

end Dat
end Lk6
