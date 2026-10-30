-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLShapeBoolsLaid.lean

It states no goal. No property of the protocol is claimed.

A SHAPE OF STATEMENT, BOOK AND COUNT OF
ROOTS (`CoreSh`, Johnson/Desc/Ground/Shape/Core.lean) WHOSE LAST GROUP, LAST TWO MESSAGES, LAST TREE AND
LAST TWO PLACES ARE KNOWN (`ClosingGroupLaid`, LotLShapeLaidForm.lean) IS, AS AN EQUATION, A TERM IN WHICH
ALL THAT STANDS IN FRONT OF THESE IS A LETTER. All at letters. Two definitions, two theorems.

  `laidBehind`          a list: the first n values of a function, then a tail
  `eq_laidBehind`       a list of length n + the tail's whose entries from n on are the tail's is
                        `laidBehind` of its own entries
  `localCore`           the term: the codes, four functions for what stands in front, the four numbers'
                        records
  `core_is_localCore`   the equation

Why. A public test on the shape that reads, of the lists, these last entries and the lengths alone can
then be put to Lean's kernel once, with the four functions as free letters
(LotLShapeBoolsClosed.lean): the kernel passes over an entry in front without looking into it.

Limits. Lists and records alone. No state is shown to meet `ClosingGroupLaid`. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLShapeLaidForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.Ground.Sh (CoreSh StSh BookSh GrpSh OrcSh TreeSh)

/-- The first n values of a function, then a tail. -/
def laidBehind {α : Type} (front : ℕ → α) (n : ℕ) (tail : List α) : List α :=
  (List.range n).map front ++ tail

/-- **A list whose entries from n on are the tail's.** d: any value. -/
theorem eq_laidBehind {α : Type} (l : List α) (n : ℕ) (tail : List α) (d : α)
    (hlen : l.length = n + tail.length) (hget : ∀ i, i < tail.length → l[n + i]? = tail[i]?) :
    l = laidBehind (fun i => l.getD i d) n tail := by
  unfold laidBehind
  have hn : ((List.range n).map fun i => l.getD i d).length = n := by
    rw [List.length_map, List.length_range]
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < n
  · have hl : i < l.length := by omega
    have e : ((List.range n).map (fun i => l.getD i d) ++ tail)[i]? =
        ((List.range n).map fun i => l.getD i d)[i]? :=
      List.getElem?_append_left (by rw [hn]; exact hi)
    have er : (List.range n)[i]? = some i := by simp [hi]
    rw [e, List.getElem?_map, er, Option.map_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hl, Option.getD_some]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : ((List.range n).map (fun i => l.getD i d) ++ tail)[n + j]? = tail[j]? := by
      rw [List.getElem?_append_right (by rw [hn]; exact Nat.le_add_right _ _), hn,
        Nat.add_sub_cancel_left]
    rw [e]
    by_cases hj : j < tail.length
    · exact hget j hj
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **The term.** -/
def localCore (codes : OnBytes.Codes) (frontMessages : ℕ → OrcSh) (frontGroups : ℕ → GrpSh)
    (frontTrees : ℕ → TreeSh) (frontPlaces : ℕ → ℕ × ℕ) (group carrier tree roots : ℕ) (G : GrpSh)
    (x z : OrcSh) (T : TreeSh) : CoreSh :=
  ⟨⟨codes, laidBehind frontMessages carrier [x, z], laidBehind frontGroups group [G]⟩,
    ⟨laidBehind frontTrees tree [T], laidBehind frontPlaces carrier [(tree, 0), (tree, 1)]⟩, roots⟩

/-- **The equation.** -/
theorem core_is_localCore {c : CoreSh} {group carrier mask tree : ℕ} {G : GrpSh} {x z : OrcSh}
    {T : TreeSh} (h : ClosingGroupLaid c group carrier mask tree G x z T) :
    c = localCore c.st.codes (fun i => c.st.oracles.getD i x) (fun i => c.st.groups.getD i G)
      (fun i => c.book.trees.getD i T) (fun i => c.book.place.getD i (0, 0)) group carrier tree
      c.roots G x z T := by
  obtain ⟨hG, hx, hz, hT, hpx, hpz, rfl, nG, nO, nP, nT⟩ := h
  have two : ∀ {α : Type} (l : List α) (a b : α), l[carrier]? = some a → l[carrier + 1]? = some b →
      ∀ i, i < [a, b].length → l[carrier + i]? = [a, b][i]? := by
    intro α l a b ha hb i hi
    have hi' : i < 2 := hi
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact ha
    · exact hb
  have one : ∀ {α : Type} (l : List α) (n : ℕ) (a : α), l[n]? = some a →
      ∀ i, i < [a].length → l[n + i]? = [a][i]? := by
    intro α l n a ha i hi
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    exact ha
  have eO := eq_laidBehind c.st.oracles carrier [x, z] x (by rw [nO]; rfl) (two _ _ _ hx hz)
  have eG := eq_laidBehind c.st.groups group [G] G (by rw [nG]; rfl) (one _ _ _ hG)
  have eT := eq_laidBehind c.book.trees tree [T] T (by rw [nT]; rfl) (one _ _ _ hT)
  have eP := eq_laidBehind c.book.place carrier [(tree, 0), (tree, 1)] (0, 0) (by rw [nP]; rfl)
    (two _ _ _ hpx hpz)
  unfold localCore
  rw [← eO, ← eG, ← eT, ← eP]

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.laidBehind
#print axioms ProofFile.Honest.K12.LotL.eq_laidBehind
#print axioms ProofFile.Honest.K12.LotL.localCore
#print axioms ProofFile.Honest.K12.LotL.core_is_localCore
