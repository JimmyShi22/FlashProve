-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TableChain.lean: in the table of the plain data of a file (`Three.Whole.of`) the tree
number j stands with the chain that sent it; so `runOfTree W r j` (OnBytes/Maker/Tables.lean) is
the run's value of the chain that `TreeAt` (OnBytes/Maker/OneRoot.lean) names at j.

Statements and proofs. The table lists the first chain's trees, then the second's, then the third's,
each with its chain's number; a chain has as many trees as its rounds have items of the kind root.

Main names:
  `treesOfChain_chain`, `treesOfChain_length`: one chain's rows.
  `trees_count`: the rows of a chain's data made from the rounds R are as many as R has roots.
  `table_chain`: the row at the number of the n-th tree of chain c has the chain c.
  `runOfTree_of_treeAt`: where `TreeAt W r j root start` (OnBytes/Maker/OneRoot.lean) holds,
    `runOfTree W r j = some start`.
  `opensTree_run`: an opening under the number j that `OpensTree` speaks of is what the reader of an
    opening hands out at the start `runOfTree W r j`.
Under "there is": in `table_chain` the row, fixed by the table's entry at the number; in
`opensTree_run` the start, fixed by `runOfTree W r x.1 = some start`, and cfg, the field, the bytes
of a salt, the file and the place of the reader's call, which nothing else ties.
Limits: no reader, no hash call and no typed salt stand in `runOfTree_of_treeAt`. That the start
which the tables lay before a leaf's salt is the start at which the reader hashed the leaf rests on
four things together: `own_treeAt` (OnBytes/Maker/OneRoot.lean, under `SrcFits`), this file,
`own_leaf` (OnBytes/Maker/ReadLeaf.lean), and `tableOfFull_makes` with
`table_listed` (OnBytes/Maker/TablesTwice.lean); no one statement lays them together. That the data
count the three chains' roots as read is a premise (for chains read under descriptions made from the
data's own rounds: OnBytes/Maker/ReadSpecs.lean, `readChain_roots`). Nothing on soundness.


-/
import OnBytes.Maker.OneRoot
import OnBytes.Maker.ReadData

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Three (treesOfChain rdsFromL rdOf rootsIn wholeNo)
open OnBytes.Params (Rounds)

/-- Every row of a chain's trees has the chain's number. -/
theorem treesOfChain_chain (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (here base : ℕ)
    (ds : List Three.RDL) : ∀ t ∈ treesOfChain all here base ds, t.chain = here := by
  intro t ht
  unfold treesOfChain at ht
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 ht
  rfl

theorem rows_length : ∀ (ds : List Three.RDL) (k : ℕ),
    ((ds.zipIdx k).flatMap fun d => d.1.trees.zipIdx.map fun s => (d.2, s.2, s.1)).length =
      (ds.map (·.trees.length)).sum
  | [], _ => rfl
  | d :: ds, k => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, rows_length ds (k + 1),
      List.length_map, List.length_zipIdx, List.map_cons, List.sum_cons]

/-- A chain has as many rows as its rounds' data have trees. -/
theorem treesOfChain_length (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (here base : ℕ)
    (ds : List Three.RDL) :
    (treesOfChain all here base ds).length = (ds.map (·.trees.length)).sum := by
  unfold treesOfChain
  rw [List.length_map, List.length_zipIdx]
  exact rows_length ds 0

/-- The rows of a chain's data made from the rounds R are as many as R has roots. -/
theorem trees_count (all all' : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first base' : ℕ)
    (R : Rounds) :
    (treesOfChain all' here base' (rdsFromL all t₁ t₂ here base first R)).length = rootsIn R := by
  rw [treesOfChain_length, rdsFromL_map all t₁ t₂ here base first (·.trees.length)
    (fun r => r.1.items.countP (· == .root)) (fun r n => by
      show ((List.range _).map _).length = _
      rw [List.length_map, List.length_range]) R]
  rfl

/-- The first, the second or the third. -/
def pick3 {α : Type} (a b c : α) : ℕ → α
  | 0 => a
  | 1 => b
  | _ => c

/-- A place in three lists laid behind each other. -/
theorem get_three {α : Type} (A B C : List α) : ∀ (c n : ℕ), c ≤ 2 →
    n < (pick3 A B C c).length →
    ∃ t, (A ++ (B ++ C))[wholeNo A.length B.length (c, n)]? = some t ∧ t ∈ pick3 A B C c
  | 0, n, _, h => by
    have h' : n < A.length := h
    refine ⟨A[n], ?_, List.getElem_mem h'⟩
    show (A ++ (B ++ C))[0 + n]? = _
    rw [Nat.zero_add, List.getElem?_append_left h', List.getElem?_eq_getElem h']
  | 1, n, _, h => by
    have h' : n < B.length := h
    refine ⟨B[n], ?_, List.getElem_mem h'⟩
    show (A ++ (B ++ C))[A.length + n]? = _
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left h', List.getElem?_eq_getElem h']
  | 2, n, _, h => by
    have h' : n < C.length := h
    refine ⟨C[n], ?_, List.getElem_mem h'⟩
    show (A ++ (B ++ C))[A.length + B.length + n]? = _
    rw [List.getElem?_append_right (by omega),
      show A.length + B.length + n - A.length = B.length + n from by omega,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem h']
  | _ + 3, _, h, _ => by omega

/-- **The row at the number of the n-th tree of chain c has the chain c.** -/
theorem table_chain (R₁ R₂ R₃ : Rounds) (c n : ℕ) (hc : c ≤ 2)
    (hn : n < pick3 (rootsIn R₁) (rootsIn R₂) (rootsIn R₃) c) :
    ∃ t, (Three.Whole.of R₁ R₂ R₃).table[wholeNo (Three.Whole.of R₁ R₂ R₃).t₁
      (Three.Whole.of R₁ R₂ R₃).t₂ (c, n)]? = some t ∧ t.chain = c := by
  have l₁ : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0
      (Three.Whole.of R₁ R₂ R₃).ds₁).length = rootsIn R₁ := trees_count _ _ _ _ _ _ _ _ R₁
  have l₂ : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁)
      (Three.Whole.of R₁ R₂ R₃).ds₂).length = rootsIn R₂ := trees_count _ _ _ _ _ _ _ _ R₂
  have l₃ : (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
      (Three.Whole.of R₁ R₂ R₃).ds₃).length = rootsIn R₃ := trees_count _ _ _ _ _ _ _ _ R₃
  have hl : n < (pick3
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 0 0 (Three.Whole.of R₁ R₂ R₃).ds₁)
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 1 (rootsIn R₁) (Three.Whole.of R₁ R₂ R₃).ds₂)
      (treesOfChain (Three.Whole.of R₁ R₂ R₃).opens 2 (rootsIn R₁ + rootsIn R₂)
        (Three.Whole.of R₁ R₂ R₃).ds₃) c).length := by
    rcases c with _ | _ | _ | c
    · exact l₁ ▸ hn
    · exact l₂ ▸ hn
    · exact l₃ ▸ hn
    · omega
  obtain ⟨t, h1, h2⟩ := get_three _ _ _ c n hc hl
  rw [l₁, l₂] at h1
  refine ⟨t, h1, ?_⟩
  rcases c with _ | _ | _ | c
  · exact treesOfChain_chain _ _ _ _ t h2
  · exact treesOfChain_chain _ _ _ _ t h2
  · exact treesOfChain_chain _ _ _ _ t h2
  · omega

/-- **The start that the tables lay is the sender's run's value.** -/
theorem runOfTree_of_treeAt {R₁ R₂ R₃ : Rounds} {r : Proof.TailRead}
    (h₁ : rootsIn R₁ = r.first.roots.length) (h₂ : rootsIn R₂ = r.shared.roots.length)
    (h₃ : rootsIn R₃ = r.second.roots.length) {j : ℕ} {root start : ByteArray}
    (T : TreeAt (Three.Whole.of R₁ R₂ R₃) r j root start) :
    runOfTree (Three.Whole.of R₁ R₂ R₃) r j = some start := by
  obtain ⟨c, n, e, hc, hr, hs⟩ := T
  have ln := lt_of_getElem? hr
  obtain ⟨t, ht, hch⟩ := table_chain R₁ R₂ R₃ c n hc (by
    rcases c with _ | _ | _ | c
    · exact h₁ ▸ ln
    · exact h₂ ▸ ln
    · exact h₃ ▸ ln
    · omega)
  unfold runOfTree
  rw [e, ht]
  show (chainOf r t.chain).run = some start
  rw [hch]
  exact hs

/-- An opening under the number j is what the reader of an opening hands out at the start that the
tables lay. -/
theorem opensTree_run {R₁ R₂ R₃ : Rounds} {r : Proof.TailRead}
    (h₁ : rootsIn R₁ = r.first.roots.length) (h₂ : rootsIn R₂ = r.shared.roots.length)
    (h₃ : rootsIn R₃ = r.second.roots.length) {x : ℕ × Opened}
    (O : OpensTree (Three.Whole.of R₁ R₂ R₃) r x) :
    ∃ start, runOfTree (Three.Whole.of R₁ R₂ R₃) r x.1 = some start ∧
      ∃ (cfg : ByteArray) (f : Fmt.Fld) (salt : ℕ) (b : ByteArray) (i : ℕ),
        Fmt.readOpeningW (m := Id) Fmt.formatHash cfg f salt x.2.1 start x.2.2.1 b i = some x.2.2.2 := by
  obtain ⟨start, T, rest⟩ := O
  exact ⟨start, runOfTree_of_treeAt h₁ h₂ h₃ T, rest⟩

end OnBytes.Maker
