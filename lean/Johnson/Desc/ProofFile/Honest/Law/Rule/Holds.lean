-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Holds.lean: what has been produced before a part holds a
column for every read that the part's own rounds make of a stored table or of a tree that was sent
before (Honest/Side.lean: `Before.holds`, a hypothesis of `Good.exact`). It is the eighth piece of
the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to `RowOk`).

  1  `any_of_find`   a small lemma
  2  `treeCols_front`   the columns listed of a tree, in what a part of chain number ch is given
  3  `holds_at`   the main lemma: from conditions on each read, which its docstring lists

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)

variable {Xi : Type}

theorem any_of_find {α β : Type} {l : List α} {p : α → Bool} {f : α → β} {b : β}
    (h : (l.find? p).map f = some b) : l.any p = true := by
  cases hf : l.find? p with
  | none =>
    rw [hf] at h
    cases h
  | some a => exact List.any_eq_true.2 ⟨a, List.mem_of_find?_eq_some hf, List.find?_some hf⟩

/-- **The columns listed of tree number j of chain number c**, in what a part of chain number ch is
given: those of its own chain; in the second chain those of all three. -/
theorem treeCols_front (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (Nat × Nat × List UInt64)) (ch c j : Nat) (hc : c ≤ 2) (hv : c = ch ∨ ch = 2) :
    ((laidOf F ρ l₀ l₁ l₂).front ch st).treeCols c j =
      ((allTabs (pick3 l₀ l₁ l₂ c))[j]?).map fun T => colsOfT T (treeAsks F ρ c j) := by
  have h0 : ∀ (t : Nat → List Nat) (l : List Played),
      ((shownBy c t l 0).flatMap (·.2.1.cols))[j]? =
        ((allTabs l)[j]?).map fun T => colsOfT T (t j) := by
    intro t l
    have := cols_at c t l 0 j
    rw [Nat.zero_add] at this
    exact this
  rcases hv with rfl | rfl
  · have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases hc3 with rfl | rfl | rfl
    · show (((shownBy 0 (treeAsks F ρ 0) l₀ 0).filter fun r => r.1 == 0).flatMap
        fun r => r.2.1.cols)[j]? = _
      rw [filter_same]
      exact h0 _ _
    · show (((shownBy 1 (treeAsks F ρ 1) l₁ 0).filter fun r => r.1 == 1).flatMap
        fun r => r.2.1.cols)[j]? = _
      rw [filter_same]
      exact h0 _ _
    · exact treeCols_at F ρ l₀ l₁ l₂ st 2 j hc
  · exact treeCols_at F ρ l₀ l₁ l₂ st c j hc

/-- **`Before.holds`.** `l₀`, `l₁`, `l₂`: the rounds produced so far. The hypothesis, on each read
that these rounds make at these challenges: it is among the reads of the whole run; a stored column
is available; a tree is one that a part of this chain is shown; where a tree of that number is
listed, a prover's side sent its table; and a tree of another chain is listed. -/
theorem holds_at (F : FileDescription Xi) (ρ : Draws) (stored : Nat → Nat → Option (List UInt64))
    (l₀ l₁ l₂ : List Played) (ch ft : Nat) (decls : List Fmt.DeclaredRound) (ds : List Fmt.Drawn)
    (h : ∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) decls ds, q ∈ allBare F ρ ∧
      (∀ i, q.item = some i → (stored i q.pos).isSome = true) ∧
      ∀ c j, q.item = none → q.src = some (c, j) → c ≤ 2 ∧ (c = ch ∨ ch = 2) ∧
        (∀ T, (allTabs (pick3 l₀ l₁ l₂ c))[j]? = some T → T.isSome = true) ∧
        (c ≠ ch → ((allTabs (pick3 l₀ l₁ l₂ c))[j]?).isSome = true)) :
    ((laidOf F ρ l₀ l₁ l₂).front ch (storedShown stored (storedAsks F ρ))).holds ch ft decls ds =
      true := by
  unfold Before.holds
  refine List.all_eq_true.2 fun q hq => ?_
  obtain ⟨hb, h1, h2⟩ := h q hq
  have hst : ((laidOf F ρ l₀ l₁ l₂).front ch (storedShown stored (storedAsks F ρ))).stored =
      storedShown stored (storedAsks F ρ) := by
    unfold Laid.front
    split
    · rfl
    · split <;> rfl
  cases hi : q.item with
  | some i =>
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (h1 i hi)
    show (((laidOf F ρ l₀ l₁ l₂).front ch (storedShown stored (storedAsks F ρ))).stored.any
      fun c => c.1 == i && c.2.1 == q.pos) = true
    rw [hst]
    exact any_of_find (find_stored stored i q.pos w hw _ (mem_storedAsks F ρ q hb i hi))
  | none =>
    cases hs : q.src with
    | none => rfl
    | some cj =>
      obtain ⟨c, j⟩ := cj
      obtain ⟨g1, g2, g3, g4⟩ := h2 c j hi hs
      show (match ((laidOf F ρ l₀ l₁ l₂).front ch
          (storedShown stored (storedAsks F ρ))).treeCols c j with
        | some cols => cols.any fun c => c.1 == q.pos
        | none => c == ch) = true
      rw [treeCols_front F ρ l₀ l₁ l₂ _ ch c j g1 g2]
      cases ht : (allTabs (pick3 l₀ l₁ l₂ c))[j]? with
      | none =>
        show (c == ch) = true
        by_cases hcc : c = ch
        · rw [hcc]
          exact beq_self_eq_true _
        · have := g4 hcc
          rw [ht] at this
          cases this
      | some T =>
        obtain ⟨T', hT'⟩ := Option.isSome_iff_exists.1 (g3 T ht)
        subst hT'
        show ((colsOfT (some T') (treeAsks F ρ c j)).any fun c => c.1 == q.pos) = true
        exact any_of_find (find_col T' q.pos _ (mem_treeAsks F ρ q hb c j hs))

end ProofFile.Honest

#print axioms ProofFile.Honest.any_of_find
#print axioms ProofFile.Honest.treeCols_front
#print axioms ProofFile.Honest.holds_at
