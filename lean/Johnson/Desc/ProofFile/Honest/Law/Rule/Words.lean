-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Words.lean: in what three chains' rounds as played show
(`laidOf`), the words of a read that is among the description's own are found, and they are the
read's own words, as `readsOf` (Honest/Frame.lean) takes them from the tables (`faith_one`). No
coin, no part and no run of a protocol occurs here.

  1  `laidOf`, `pick3`, `treeCols_at`   what three chains' rounds show, at the positions that the
     description's declared rounds read at given challenges; the columns listed of a tree
  2  `mem_treeAsks`, `mem_storedAsks`   a read's position is among the positions read
  3  `faith_one`   the main lemma

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place OpenedColumn)

variable {Xi : Type}

/-! ## 1 What three chains' rounds show -/

/-- What three chains' rounds as played show, each tree at all positions that are read of it. -/
def laidOf (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played) : Laid :=
  ⟨shownBy 0 (treeAsks F ρ 0) l₀ 0, shownBy 1 (treeAsks F ρ 1) l₁ 0,
    shownBy 2 (treeAsks F ρ 2) l₂ 0⟩

/-- One of three, by a chain's number: 0, 1, and any other number. -/
def pick3 {α : Type} (a b c : α) (ch : Nat) : α := if ch == 0 then a else if ch == 1 then b else c

/-- **The columns listed of tree number j of chain number c** (c at most 2), in the cut for the
second chain, are those of the table of that number among the chain's rounds, at the positions read
of it; `none` if the chain sent fewer. -/
theorem treeCols_at (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (Nat × Nat × List UInt64)) (c j : Nat) (hc : c ≤ 2) :
    ((laidOf F ρ l₀ l₁ l₂).front 2 st).treeCols c j =
      ((allTabs (pick3 l₀ l₁ l₂ c))[j]?).map fun T => colsOfT T (treeAsks F ρ c j) := by
  have h0 : ∀ (t : Nat → List Nat) (l : List Played),
      ((shownBy c t l 0).flatMap (·.2.1.cols))[j]? =
        ((allTabs l)[j]?).map fun T => colsOfT T (t j) := by
    intro t l
    have := cols_at c t l 0 j
    rw [Nat.zero_add] at this
    exact this
  show (((shownBy 0 (treeAsks F ρ 0) l₀ 0 ++ shownBy 1 (treeAsks F ρ 1) l₁ 0 ++
    shownBy 2 (treeAsks F ρ 2) l₂ 0).filter fun r => r.1 == c).flatMap fun r => r.2.1.cols)[j]? = _
  rw [List.filter_append, List.filter_append]
  have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hc3 with rfl | rfl | rfl
  · rw [filter_same, filter_other (ch := 1) (c := 0) (by decide),
      filter_other (ch := 2) (c := 0) (by decide), List.append_nil, List.append_nil]
    exact h0 _ _
  · rw [filter_other (ch := 0) (c := 1) (by decide), filter_same,
      filter_other (ch := 2) (c := 1) (by decide), List.nil_append, List.append_nil]
    exact h0 _ _
  · rw [filter_other (ch := 0) (c := 2) (by decide), filter_other (ch := 1) (c := 2) (by decide),
      filter_same, List.nil_append, List.nil_append]
    exact h0 _ _

/-! ## 2 A read's position is among the positions read -/

theorem mem_treeAsks (F : FileDescription Xi) (ρ : Draws) (q : Read) (hq : q ∈ allBare F ρ) (c j : Nat)
    (hs : q.src = some (c, j)) : q.pos ∈ treeAsks F ρ c j := by
  unfold treeAsks
  exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨hq, by rw [hs]; simp⟩, rfl⟩

theorem mem_storedAsks (F : FileDescription Xi) (ρ : Draws) (q : Read) (hq : q ∈ allBare F ρ) (i : Nat)
    (hi : q.item = some i) : (i, q.pos) ∈ storedAsks F ρ := by
  unfold storedAsks
  exact List.mem_filterMap.2 ⟨q, hq, by rw [hi]; rfl⟩

/-! ## 3 The main lemma -/

/-- **A read's own words are found in what has been produced.** `tr`: the table behind a source, as
the reads were made. `htr`: it is the table of that number among the rounds of the chain that sent
it. `hb`: without its sender and words the read is one that F's declared rounds make at ρ
(`allBare`); `decls`, `own`, `ch` and `ft`, at which the read was made, are tied to F and ρ by that
alone. The words are looked up in the cut for the second chain (`front 2`: all three chains'
rounds), at the stored columns `storedShown stored (storedAsks F ρ)`. -/
theorem faith_one (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (stored : Nat → Nat → Option (List UInt64)) (ch ft : Nat)
    (tr : Fmt.TreeSource → Option (Place × Table)) (decls : List Fmt.DeclaredRound)
    (own : List Fmt.Drawn)
    (htr : ∀ o pT, tr o = some pT → (srcOf ch o).1 ≤ 2 ∧
      ((allTabs (pick3 l₀ l₁ l₂ (srcOf ch o).1))[(srcOf ch o).2]?).join = some pT.2)
    (q : Read) (hq : q ∈ readsOf ch ft stored tr decls own) (hb : q.bare ∈ allBare F ρ)
    (w : List UInt64) (hw : q.words = some w) :
    ((laidOf F ρ l₀ l₁ l₂).front 2 (storedShown stored (storedAsks F ρ))).wordsAt q.bare =
      some w := by
  rcases readsOf_form ch ft stored tr decls own q hq with ⟨i, h1, -, h3⟩ | ⟨o, h1, h2, h3⟩
  · have hi : q.bare.item = some i := h1
    unfold Before.wordsAt
    rw [hi]
    show (((storedShown stored (storedAsks F ρ)).find? fun c =>
      c.1 == i && c.2.1 == q.pos).map (·.2.2)) = some w
    exact find_stored stored i q.pos w (h3.symm.trans hw) _ (mem_storedAsks F ρ q.bare hb i hi)
  · have hi : q.bare.item = none := h1
    have hs : q.bare.src = some ((srcOf ch o).1, (srcOf ch o).2) := h2
    rw [hw] at h3
    cases hto : tr o with
    | none =>
      rw [hto] at h3
      cases h3
    | some pT =>
      rw [hto] at h3
      have hwT : w = pT.2.col q.pos := Option.some.inj h3
      obtain ⟨hle, htab⟩ := htr o pT hto
      have hcols := treeCols_at F ρ l₀ l₁ l₂ (storedShown stored (storedAsks F ρ))
        (srcOf ch o).1 (srcOf ch o).2 hle
      have hget : (allTabs (pick3 l₀ l₁ l₂ (srcOf ch o).1))[(srcOf ch o).2]? =
          some (some pT.2) := by
        cases hg : (allTabs (pick3 l₀ l₁ l₂ (srcOf ch o).1))[(srcOf ch o).2]? with
        | none =>
          rw [hg] at htab
          cases htab
        | some t =>
          rw [hg] at htab
          exact congrArg some htab
      rw [hget] at hcols
      unfold Before.wordsAt
      rw [hi, hs]
      show ((((laidOf F ρ l₀ l₁ l₂).front 2 (storedShown stored (storedAsks F ρ))).treeCols
        (srcOf ch o).1 (srcOf ch o).2).bind fun cols =>
          (cols.find? fun c => c.1 == q.pos).map (·.2)) = some w
      rw [hcols, hwT]
      exact find_col pT.2 q.pos _ (mem_treeAsks F ρ q.bare hb _ _ hs)

end ProofFile.Honest

#print axioms ProofFile.Honest.treeCols_at
#print axioms ProofFile.Honest.mem_treeAsks
#print axioms ProofFile.Honest.mem_storedAsks
#print axioms ProofFile.Honest.faith_one
