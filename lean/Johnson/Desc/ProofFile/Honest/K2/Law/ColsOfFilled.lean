-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ColsOfFilled.lean: the kind "the code switch" (K2): THE COLUMNS
THAT THE FRAME FILLS FOR A SWITCH's TWO ROUNDS (`fillCols` of `readsOf`,
Johnson/Desc/ProofFile/Honest/Frame.lean) ARE THE COLUMNS OF THE TABLES AT HAND, EACH UNDER ITS OWN
TREE's NUMBER: `ColsOf` (Johnson/Top/H0/K2Hears/LongCols.lean) AT A READING OF THE TABLES THAT IS
WRITTEN OUT; AND SO ARE THE COLUMNS THAT THE KIND's TEXT LAYS FLAT AGAIN BEHIND THE STEP's OWN
TESTS. Four lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `fillCols_mem`  without a stored run each filled column is a read's own words, at its key and
      position
  `readsOf_switch`  what a switch's two rounds (`rounds`, Johnson/Top/H0/Tw/K2C/Kind.lean) read
  **`colsOf_filled`**  `ColsOf (fun key x => ((tree (.own key)).map (·.2.col x)).getD []) cols`
  `colsOf_flat`  `ColsOf` passes from the columns handed to `flat q (b.shown q.firstTree rs cols)`:
      by the sealed `flat_sub` (Johnson/Top/H0/K2Hears/ColsAtStage.lean)
Kin. `fillCols_words` (Honest/K14/ColsPaid.lean): the words and the position of a read, not
its key. `fillCols_kept` (Honest/Law/Cols.lean): keys, positions and widths, as lists. `fill_words`
(Honest/Law/Rule/ChainEnd.lean): each read has words. None gives the key and the words of one read.
Limits. «NOT IN FRONT OF A LAW OVER COINS». THE GROUND, of the first kind: cols stands under h: an
equation between it and what `readsOf` takes out of `tree`, which "for all" binds here and which in
a run comes of coins. Made term and lemma that lift the bar: none: the bar is flat. The written
reading answers [] at a source behind which `tree` has nothing. No column of cols comes from there:
at a read whose `words` is `none`, with an empty stored run, `fillCols` ends in its error "a column
is read of a table that is not at hand". The first tree's number is the plan's own (q.firstTree).
`Block.Fits` is a premise of `colsOf_flat`.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Frame
import Johnson.Top.H0.K2Hears.ColsAtStage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First.K2 (P2 rounds flat ColsOf flat_sub)

/-- Without a stored run each filled column is a read's own words, at its key and position. -/
theorem fillCols_mem : ∀ (reads : List Read) (cols : List OpenedColumn), fillCols reads [] = .ok cols →
    ∀ c ∈ cols, ∃ r ∈ reads, r.words = some c.2.2 ∧ c.1 = r.key ∧ c.2.1 = r.pos
  | [], cols, h, c, hc => by
    obtain rfl : [] = cols := Except.ok.inj h
    cases hc
  | r :: rs, cols, h, c, hc => by
    unfold fillCols at h
    cases hw : r.words with
    | none =>
      rw [hw] at h
      cases h
    | some w =>
      rw [hw] at h
      dsimp only at h
      split at h
      · cases h
      · cases hl : fillCols rs ([] : List OpenedColumn).tail with
        | error e =>
          rw [hl] at h
          cases h
        | ok l =>
          rw [hl] at h
          obtain rfl : (r.key, r.pos, w) :: l = cols := Except.ok.inj h
          rcases List.mem_cons.1 hc with rfl | hc'
          · exact ⟨r, List.mem_cons_self, hw, rfl, rfl⟩
          · obtain ⟨r', h1, h2⟩ := fillCols_mem rs l hl c hc'
            exact ⟨r', List.mem_cons_of_mem _ h1, h2⟩

/-- What a code switch's two rounds read. -/
theorem readsOf_switch (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (q : P2) (R1 R2 : Fmt.Drawn) (r : Read)
    (hr : r ∈ readsOf chain ft stored tree (rounds q) [R1, R2]) :
    ∃ n ∈ q.read, r.key = q.firstTree + n.1 - ft ∧
      r.words = (tree (.own n.1)).map (·.2.col r.pos) := by
  simp only [readsOf, rounds, List.flatMap_nil, List.nil_append, List.append_nil,
    List.flatMap_map, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨n, hn, x, -, rfl⟩ := hr
  exact ⟨n, hn, rfl, rfl⟩

/-- **The filled columns are the tables' own.** -/
theorem colsOf_filled (chain : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (q : P2) (R1 R2 : Fmt.Drawn) (cols : List OpenedColumn)
    (h : fillCols (readsOf chain q.firstTree stored tree (rounds q) [R1, R2]) [] = .ok cols) :
    ColsOf (fun key x => ((tree (.own key)).map (·.2.col x)).getD []) cols := by
  intro c hc
  obtain ⟨r, hr, hw, hk, hp⟩ := fillCols_mem _ _ h c hc
  obtain ⟨n, -, e1, e2⟩ := readsOf_switch _ _ _ _ _ _ _ r hr
  rw [hk, hp, e1, Nat.add_sub_cancel_left]
  show c.2.2 = ((tree (.own n.1)).map (·.2.col r.pos)).getD []
  rw [← e2, hw]
  rfl

/-- **So are the columns that the kind's text lays flat again**, behind the step's own tests. -/
theorem colsOf_flat {S Cl : Type} (b : Block S Cl) (q : P2) (hr : b.rounds = rounds q)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : b.Fits q.firstTree rs cols)
    (orc : Nat → Nat → List UInt64) (hc : ColsOf orc cols) :
    ColsOf orc (flat q (b.shown q.firstTree rs cols)) :=
  fun c hm => hc c (flat_sub b q hr rs cols hF c hm)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.fillCols_mem
#print axioms ProofFile.Honest.K2.readsOf_switch
#print axioms ProofFile.Honest.K2.colsOf_filled
#print axioms ProofFile.Honest.K2.colsOf_flat
