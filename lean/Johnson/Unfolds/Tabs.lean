-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Unfolds/Tabs.lean: the three written tables of 65,536 words in what the first half of the
layers' layout returns have that many words, each below the prime. Statements with their proofs;
nothing is evaluated.
  `word_ok` | `table_ok`: a number below 2 ^ 42, as a word, is below the prime; so a table made of
    a rule whose values are below 2 ^ 42. `getD_le` | `siluWord_le`: bounds for the third table.
  `fc_ok`: the table FC, at every shape. `fl_ok`: the table FL, WHERE smax ≤ 4095.
  `fs_ok`: the table FS, WHERE eg = 8, smax = 4095, and the profile has routed experts and the
    gate's clamp (p3 and gcl): one setting, not every shape.

Limits. Each of the three asks that layoutBase has returned. Nothing on soundness.
-/
import Johnson.Goal.Meaning.PadScope
import Johnson.Meaning.GateLut
import Johnson.Desc.Sound.RuleAtKitProofs

set_option autoImplicit false

namespace Johnson.Unfolds
open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- A number below 2 ^ 42, as a word, is below the prime. -/
theorem word_ok {n : Nat} (h : n < 2 ^ 42) : okF n.toUInt64 = true := by
  refine VerifiableInference.Desc.Sound.okF_of_lt _ ?_
  have e : n.toUInt64.toNat = n % 2 ^ 64 := by simp [Nat.toUInt64]
  rw [e, Nat.mod_eq_of_lt (by omega)]
  have : Fmt.Fld.two.p = 18446744069414584321 := by decide
  omega

/-- A table made of a rule over the first n numbers: its size; its words. -/
theorem table_ok (f : Nat → Nat) (n : Nat) (h : ∀ t, t < n → f t < 2 ^ 42) :
    ((Array.range n).map fun t => (f t).toUInt64).size = n ∧
      ∀ x ∈ ((Array.range n).map fun t => (f t).toUInt64).toList, okF x = true := by
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  exact word_ok (h t ht)

theorem getD_le {a : Array Nat} {B : Nat} (h : ∀ v ∈ a.toList, v ≤ B) (t : Nat) :
    a.getD t 0 ≤ B := by
  by_cases ht : t < a.size
  · have e : a.getD t 0 = a[t] := by simp [Array.getD, ht]
    rw [e]
    exact h _ (Array.getElem_mem_toList ht)
  · have e : a.getD t 0 = 0 := by simp [Array.getD, ht]
    rw [e]
    exact Nat.zero_le _

/-- A word of table SILU is at most 4096 + smax. -/
theorem siluWord_le (eg smax : Nat) (X : Array Nat) (t : Nat) :
    siluWord eg smax X t ≤ 4096 + smax := by
  unfold siluWord
  dsimp only
  split
  · omega
  · have := Nat.min_le_right (roundHalfUp 64 (roundD
      ((if decide (t < 32768) = true then min (32768 - t) (64 * 2 ^ eg)
        else min (t - 32768) (64 * 2 ^ eg - 1)) *
        (onePlusExp X (if decide (t < 32768) = true then min (32768 - t) (64 * 2 ^ eg)
          else min (t - 32768) (64 * 2 ^ eg - 1)) (decide (t < 32768))).2)
      (2 ^ eg * (onePlusExp X (if decide (t < 32768) = true then min (32768 - t) (64 * 2 ^ eg)
          else min (t - 32768) (64 * 2 ^ eg - 1)) (decide (t < 32768))).1))) smax
    omega

variable {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}

theorem fc_ok (hy : layoutBase h pc = .ok y) :
    y.tauFC.size = 65536 ∧ ∀ x ∈ y.tauFC.toList, okF x = true := by
  rw [OnBytes.Road.Hd.tauFC_of_base hy]
  exact table_ok rowFC 65536 fun t ht =>
    Nat.lt_trans (OnBytes.Road.Hd.rowFC_lt ht) (by decide)

theorem fl_ok (hy : layoutBase h pc = .ok y) (hs : h.smax ≤ 4095) :
    y.tauFL.size = 65536 ∧ ∀ x ∈ y.tauFL.toList, okF x = true := by
  rw [(Meaning.P34.tables_of_base hy).1]
  refine table_ok (fun t => t + (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28) 65536
    fun t ht => ?_
  have b : (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 ≤ 4096 + h.smax := by
    refine getD_le (fun v hv => ?_) t
    unfold gateTables at hv
    simp only [Array.toList_map, List.mem_map] at hv
    obtain ⟨u, _, rfl⟩ := hv
    exact siluWord_le _ _ _ _
  show t + (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28 < 2 ^ 42
  have : (gateTables h.eg h.smax h.p3 h.gcl).1.getD t 0 * 2 ^ 28 ≤ 8191 * 2 ^ 28 :=
    Nat.mul_le_mul_right _ (by omega)
  omega

theorem fs_ok (hy : layoutBase h pc = .ok y) (h1 : h.eg = 8) (h2 : h.smax = 4095)
    (h3 : h.p3 = true) (h4 : h.gcl = true) :
    y.tauFS.size = 65536 ∧ ∀ x ∈ y.tauFS.toList, okF x = true := by
  rw [(Meaning.P34.tables_of_base hy).2, h1, h2, h3, h4, if_pos rfl]
  exact table_ok (rowFS true (gateTables 8 4095 true true).2) 65536 fun t ht =>
    Nat.lt_trans (Meaning.Gate.rowFS_eq ht).2 (by decide)

end Johnson.Unfolds

#print axioms Johnson.Unfolds.word_ok
#print axioms Johnson.Unfolds.table_ok
#print axioms Johnson.Unfolds.getD_le
#print axioms Johnson.Unfolds.siluWord_le
#print axioms Johnson.Unfolds.fc_ok
#print axioms Johnson.Unfolds.fl_ok
#print axioms Johnson.Unfolds.fs_ok
