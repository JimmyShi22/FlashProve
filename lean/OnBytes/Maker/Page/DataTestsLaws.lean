-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/DataTestsLaws.lean: what the tests of OnBytes/Maker/Page/DataTests.lean give.

  `mem_of_treeShT`    the tree number n of a stretch is a tree that one of its rounds sends.
  `treesFitB_spec`    `treesFitB` gives `TreesFit` (OnBytes/Maker/Page/CodeAt.lean).
  `storedFitB_spec`   `storedFitB` gives `StoredFitE`.
  `pageFitB_spec`     `pageFitB` gives the four.
  `saltsFit_of_page`  `pageFitB` gives the test `saltsFit` (OnBytes/Maker/TablesRow.lean).

Not claimed. That a test says yes at any data.


-/
import OnBytes.Maker.Page.DataTests
import OnBytes.Maker.Page.CodeAt

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Maker

/-- The tree number n of a stretch is a tree that one of its rounds sends. -/
theorem mem_of_treeShT : ∀ (ds : List RDT) (n : ℕ) (sh : Fmt.Shape), treeShT ds n = some sh →
    ∃ d ∈ ds, sh ∈ d.trees
  | [], _, _, h => by cases h
  | d :: ds, n, sh, h => by
    rw [treeShT_cons] at h
    by_cases hn : n < d.trees.length
    · rw [if_pos hn] at h
      exact ⟨d, List.mem_cons_self, List.mem_of_getElem? h⟩
    · rw [if_neg hn] at h
      obtain ⟨d', hd', hs⟩ := mem_of_treeShT ds _ sh h
      exact ⟨d', List.mem_cons_of_mem _ hd', hs⟩

theorem two_pow_le {a : ℕ} (h : a ≤ 63) : 2 ^ a + 2 ^ a ≤ 2 ^ 64 := by
  have h1 : 2 ^ a ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) h
  omega

theorem treesFitB_spec {sb : ℕ} {ds : List RDT} (h : treesFitB sb ds = true) : TreesFit sb ds := by
  intro n sh hs
  obtain ⟨d, hd, hm⟩ := mem_of_treeShT ds n sh hs
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h d hd) sh hm
  unfold treeFitB at h1
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h1
  exact ⟨h1.1.1, two_pow_le h1.1.2, h1.2⟩

theorem storedFitB_spec {a sb : ℕ} {W : Three.Whole} (h : storedFitB a sb W = true) :
    StoredFitE a sb W := by
  unfold storedFitB at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ha, h⟩ := h
  intro d hd t ht
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h d hd) t ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩ := h1
  refine ⟨t1, t2, t3, t4, fun x col hx hc => ⟨?_, ?_, ?_⟩⟩
  · show col.length < 2 ^ 24
    rw [hc]
    exact t5
  · show 174 + 65536 * Fmt.leafPlace 0 col.length (sb / 8) < 2 ^ 64
    rw [hc]
    exact t6
  · show 2 ^ a + x < 2 ^ 64
    have := two_pow_le ha
    omega

theorem pageFitB_spec {a sb : ℕ} {W : Three.Whole} (h : pageFitB a sb W = true) :
    TreesFit sb (WholeD.of a W).ds₁ ∧ TreesFit sb (WholeD.of a W).ds₂ ∧
      TreesFit sb (WholeD.of a W).ds₃ ∧ StoredFitE a sb W := by
  unfold pageFitB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨treesFitB_spec h.1.1.1, treesFitB_spec h.1.1.2, treesFitB_spec h.1.2,
    storedFitB_spec h.2⟩

/-- The test on the stored tables' salts follows from the page's test. -/
theorem saltsFit_of_page {a sb : ℕ} {W : Three.Whole} (h : pageFitB a sb W = true) :
    saltsFit sb W = true := by
  unfold pageFitB storedFitB at h
  unfold saltsFit
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact fun d hd t ht => (h.2.2 d hd t ht).1.1.2

end OnBytes.Maker.Page
