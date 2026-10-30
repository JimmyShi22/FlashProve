-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DisciplineOpen.lean: the tokens of a tree that is taken from a list of trees (`TreeTok`,
Compile/SpecDiscipline.lean; `TreeH`, Compile/Bcs.lean). The tree `⟨[], []⟩`, which replaces a
missing one, has no tokens (`not_treeTok_default`). What `getD` or `headD` takes from a list with
that default is in the list or is that tree (`getD_mem_or`, `headD_mem_or`). So every token of it is
a token of a tree of the list (`treeTok_of_mem_or`).
-/
import Compile.Discipline

namespace Compile.Disc
open Iop Rom

variable {I X : Type} {lam K : ℕ} {p : Params}

namespace Open

theorem not_treeTok_default (u : Tok) : ¬ TreeTok (⟨[], []⟩ : TreeH lam) u := by
  rintro ⟨s, s', h, -⟩
  exact absurd h (List.not_mem_nil)

theorem getD_mem_or (trees : List (TreeH lam)) (n : ℕ) :
    trees.getD n ⟨[], []⟩ ∈ trees ∨ trees.getD n ⟨[], []⟩ = (⟨[], []⟩ : TreeH lam) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : trees[n]? with
  | none => exact Or.inr rfl
  | some t => exact Or.inl (List.mem_of_getElem? h)

theorem headD_mem_or (trees : List (TreeH lam)) :
    trees.headD ⟨[], []⟩ ∈ trees ∨ trees.headD ⟨[], []⟩ = (⟨[], []⟩ : TreeH lam) := by
  cases trees with
  | nil => exact Or.inr rfl
  | cons t l => exact Or.inl List.mem_cons_self

theorem treeTok_of_mem_or {trees : List (TreeH lam)} {t : TreeH lam} (ht : t ∈ trees ∨ t = ⟨[], []⟩)
    {u : Tok} (hu : TreeTok t u) : ∃ tr ∈ trees, TreeTok tr u := by
  rcases ht with ht | rfl
  · exact ⟨t, ht, hu⟩
  · exact absurd hu (not_treeTok_default u)

end Open

open Open

end Compile.Disc
