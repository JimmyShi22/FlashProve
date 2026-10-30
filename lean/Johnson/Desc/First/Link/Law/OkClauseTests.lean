-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/OkClauseTests.lean: THE CLAUSES OF THE PROMISE Ok ON WHICH THE EIGHT
FIELDS "fu…" OF THE THREE SORTS' TAKES REST, AS TESTS WITH CODE ON WHAT IS FIXED BEFORE THE DRAW;
EACH WITH "ITS YES GIVES THE CLAUSE's BODY". Definitions with code, and theorems. A law file; no
running text imports it. THE TEXT IS CUT OUT OF OkTests.lean
BY PROGRAM, no word turned: so that the tests hang on OnBytes/Tie/Pv/Tail/EndWhole.lean alone,
and not on FullEq.lean | FullEqUnit.lean.

The tests read: tl (the approximate range proof's structure, as the promise holds it), funs (the
list of tables), F (the snapshot's ledger), a list of forms. None reads a table's weights phi.
  `blocksB tl`, `blocks_of_test` · `posB tl funs F`, `pos_of_test` · `zOf_two` · `apartAtB tl t`,
                    `apart_at` ·
  `apartB tl`, `apart_of_test` (at every list of tables) · `uB tl i` · `entsB i F l`,
                    `ents_of_test`.

Limits. Implications. Nothing is evaluated here. Nothing on soundness or on hiding.

-/
import OnBytes.Tie.Pv.Tail.EndWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail (reads_tree)
open OnBytes.Tie.Pv.Tail.Port (readsList uOf posOf colsU)

/-! ## 1 The tests -/

/-- The structure's number of blocks is the one computed afresh. -/
def blocksB (tl : HTailF2) : Bool := decide (tl.wants.map (·.1) = some tl.zzBlocks)

theorem blocks_of_test {tl : HTailF2} (h : blocksB tl = true) :
    tl.wants.map (·.1) = some tl.zzBlocks := of_decide_eq_true h

/-- Each place that a read names lies within its table's width in the ledger. -/
def posB (tl : HTailF2) (funs : Array HFun) (F : Fork) : Bool :=
  (readsList tl funs).all fun x =>
    (List.range (tl.mats.getD x.1.mat {}).k).all fun d =>
      decide (posOf tl x.1 x.2 d < colsU F (uOf tl x.1))

theorem pos_of_test {tl : HTailF2} {funs : Array HFun} {F : Fork} (h : posB tl funs F = true) :
    ∀ x ∈ readsList tl funs, ∀ d, d < (tl.mats.getD x.1.mat {}).k →
      posOf tl x.1 x.2 d < colsU F (uOf tl x.1) := fun x hx d hd =>
  of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h x hx) d (List.mem_range.2 hd))

/-- The call of a number is the first or the second. -/
theorem zOf_two (tl : HTailF2) (k : ℕ) : tl.zOf k = tl.z1 ∨ tl.zOf k = tl.z2 := by
  unfold HTailF2.zOf
  by_cases h : (k == 0) = true
  · left; rw [if_pos h]
  · right; rw [if_neg h]

/-- The array t is one of the four vectors, and another than the digits', the planes', the symbols'
and the pieces'. -/
def apartAtB (tl : HTailF2) (t : ℕ) : Bool :=
  ((List.range 4).any fun n0 => decide (tl.ix.U.getD n0 none = some t)) &&
    decide (tl.ix.ZZ ≠ t) && decide (tl.ix.BZ ≠ t) &&
    ((List.range tl.NM).all fun mu => decide (tl.gtTree.getD mu 0 ≠ t)) &&
    (tl.z1.pieces.toList.all fun p => decide (p.tree ≠ t)) &&
    tl.z2.pieces.toList.all fun p => decide (p.tree ≠ t)

theorem apart_at {tl : HTailF2} {t : ℕ} (h : apartAtB tl t = true) :
    ∃ n0, n0 < 4 ∧ tl.ix.U.getD n0 none = some t ∧ tl.ix.ZZ ≠ t ∧ tl.ix.BZ ≠ t ∧
      (∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ t) ∧
      ∀ k p, p ∈ (tl.zOf k).pieces.toList → p.tree ≠ t := by
  unfold apartAtB at h
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨n0, a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
  refine ⟨n0, a1, a2, a3, a4, a5, fun k p hp => ?_⟩
  rcases zOf_two tl k with e | e
  · rw [e] at hp; exact a6 p hp
  · rw [e] at hp; exact a7 p hp

/-- `apartAtB` at the arrays of vector 0 and of vector 2 (number 0 where the entry is empty). -/
def apartB (tl : HTailF2) : Bool :=
  [0, 2].all fun tr => apartAtB tl ((tl.ix.U.getD tr none).getD 0)

/-- **okApart's body, at every list of tables.** -/
theorem apart_of_test {tl : HTailF2} (h : apartB tl = true) (funs : Array HFun) :
    ∀ x ∈ readsList tl funs, ∃ n0, n0 < 4 ∧ tl.ix.U.getD n0 none = some (uOf tl x.1) ∧
      tl.ix.ZZ ≠ uOf tl x.1 ∧ tl.ix.BZ ≠ uOf tl x.1 ∧
      (∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ uOf tl x.1) ∧
      ∀ k p, p ∈ (tl.zOf k).pieces.toList → p.tree ≠ uOf tl x.1 := by
  intro x hx
  have hm : x.1.tree ∈ [0, 2] := by
    rcases reads_tree tl funs x hx with e | e <;> simp [e]
  exact apart_at (List.all_eq_true.1 h _ hm)

/-- The array of the reads is vector 2. -/
def uB (tl : HTailF2) (i : ℕ) : Bool := decide (tl.ix.U.getD 2 none = some i)

/-- Every entry that a form of the list names stands at array i, virtual row 0, below the width. -/
def entsB (i : ℕ) (F : Fork) (l : List Aff) : Bool :=
  l.all fun f => f.ents.toList.all fun x =>
    decide (x.tree = i) && decide (x.row = 0) && decide (x.idx < colsU F i)

theorem ents_of_test {i : ℕ} {F : Fork} {l : List Aff} (h : entsB i F l = true) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = i ∧ x.row = 0 ∧ x.idx < colsU F i := by
  intro f hf x hx
  have a := List.all_eq_true.1 (List.all_eq_true.1 h f hf) x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at a
  exact ⟨a.1.1, a.1.2, a.2⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.apart_of_test
#print axioms VerifiableInference.Desc.LinkJoin.ents_of_test
