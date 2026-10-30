-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Catches.lean: a batched row holds at few multipliers, if one of the rows does not
hold.

The batched row is short of the sum of x^i times what row number i is short of
(Johnson/Desc/Means/Combine.lean, Bridge.lean). The library counts at how many values of one
challenge a sum of its powers times given values vanishes (Alg/Poly.lean: count_powers_le). This
file carries that count to the batching: for words of which one of n rows does not hold, the
elements of K as which x can read, if the batched row is to hold, are at most n - 1. The rows and
the words come first, x after them.

Main theorems: hornerSum_fin, count_hornerSum_le, combine_catches, combineRows_catches.

What is not claimed. Nothing on who draws x, on when it is drawn, or on how the readings of the
drawn elements are spread over K: no chance is named here. Nothing on soundness.

-/
import Johnson.Desc.Means.Bridge
import Alg.Poly

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K]

/-- The sum a_0 + y a_1 + y^2 a_2 + .., in the form in which the library counts its zeros. -/
theorem hornerSum_fin (y : K) : ∀ l : List K,
    hornerSum y l = ∑ j : Fin l.length, y ^ ((j : ℕ) + 0) * l.get j
  | [] => by simp [hornerSum]
  | a :: l => by
    have e := Fin.sum_univ_succ
      (fun j : Fin (l.length + 1) => y ^ ((j : ℕ) + 0) * (a :: l).get j)
    refine Eq.trans ?_ e.symm
    rw [hornerSum, hornerSum_fin y l]
    simp only [Fin.val_zero, Fin.val_succ, List.get_cons_zero, add_zero, pow_zero, one_mul,
      Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have eg : (a :: l).get j.succ = l.get j := rfl
    rw [eg, pow_succ]
    ring

/-- If not all rows hold of the words, one of them is short of something. -/
theorem short_ne (ρ : Reading K) {S : Statement} {l : List Row} {m : Words K}
    (hbad : ¬ AllSay ρ S l m) :
    ∃ a ∈ l.map (fun r => short ρ S r m), a ≠ 0 := by
  by_contra c
  apply hbad
  intro r hr'
  rw [says_iff_short]
  by_contra c'
  exact c ⟨_, List.mem_map.2 ⟨r, hr', rfl⟩, c'⟩

variable [IsDomain K] [Finite K]

/-- **The sum vanishes at few y**, if one of its members is not 0. -/
theorem count_hornerSum_le (l : List K) (h : ∃ a ∈ l, a ≠ 0) :
    Nat.card {y : K // hornerSum y l = 0} ≤ l.length - 1 := by
  have ha : (fun j : Fin l.length => l.get j) ≠ 0 := by
    obtain ⟨a, hmem, hne⟩ := h
    obtain ⟨j, hj⟩ := List.mem_iff_get.1 hmem
    intro c
    exact hne (by rw [← hj]; exact congrFun c j)
  have hc := Alg.count_powers_le (fun j : Fin l.length => l.get j) ha 0
  rw [Nat.add_zero] at hc
  refine le_trans (le_of_eq (Alg.count_congr fun y => ?_)) hc
  rw [hornerSum_fin]

variable (ρ : Reading K)

/-- **The batching on a group catches.** For words of which one of the rows does not hold: the
elements of K as which x reads, for some x at which Bat.combine's row holds of tables that hold the
words on the blocks, are fewer than the rows. -/
theorem combine_catches (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (rows : Array Row)
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r) (m : Words K) (hbad : ¬ AllSay ρ S rows.toList m) :
    Nat.card {y : K // ∃ (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
      Bat.combine S g ⟨L, rows⟩ x = some out ∧ LaidOn S L m T ∧ GroupSays ρ S L out T} ≤
      rows.size - 1 := by
  have h1 := count_hornerSum_le _ (short_ne ρ hbad)
  rw [List.length_map, Array.length_toList] at h1
  refine le_trans (Alg.count_mono fun y hy => ?_) h1
  obtain ⟨x, out, T, rfl, hc, hT, hs⟩ := hy
  obtain ⟨out', h', _, _, e⟩ := combine_on ρ S g G L rows x hG hL hOk hr
  rw [hc] at h'
  obtain rfl := Option.some.inj h'
  rw [← e m T hT]
  exact (groupSays_iff_short ρ S L out T).1 hs

/-- **The batching of rows that stay rows catches.** -/
theorem combineRows_catches (S : Statement) (rows : Array Row) (m : Words K)
    (hbad : ¬ AllSay ρ S rows.toList m) :
    Nat.card {y : K // ∃ x : E, ρ.val x = y ∧ Says ρ S (Bat.combineRows rows x) m} ≤
      rows.size - 1 := by
  have h1 := count_hornerSum_le _ (short_ne ρ hbad)
  rw [List.length_map, Array.length_toList] at h1
  refine le_trans (Alg.count_mono fun y hy => ?_) h1
  obtain ⟨x, rfl, hs⟩ := hy
  rw [← combineRows_means]
  exact (says_iff_short ρ S _ m).1 hs

end OnBytes.Means
