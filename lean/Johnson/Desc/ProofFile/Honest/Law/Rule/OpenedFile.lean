-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenedFile.lean: what the field `opened` holds at the start
of a file's second chain. `ChainProgress.start` (Honest/Walk.lean) lays there what it is handed; `runC` and
`midAtW` (Honest/MidW.lean) hand it the columns that the first and the shared chain have read. These
are the columns that a simulator of the second chain finds, for the two earlier chains' declared
reads, in what these two chains have produced (`tie_second`: `TieAt`,
Honest/Law/Rule/OpenedStep.lean, before the second chain's first sub-protocol). `model`
(Honest/Law/Rule/Model.lean) and `file_inv` (Honest/Law/Rule/FileInv.lean) pay `chain_file`'s and
`chain_start`'s hypothesis `htie` with it at the second chain; `tie_second_at`
(Honest/Law/Rule/OpenedRun.lean) pays `opened_at_chain`'s (Honest/Law/Rule/OpenedWalk.lean) with it.

  1  `laid_field`   the field as `ChainProgress.start` lays it
  2  `held_two`   the two earlier chains' columns, found in what they have produced. As the first
     two thirds of `views_back` (Honest/Law/Rule/Reads.lean), with nothing produced by the second
     chain
  3  `tie_second`   the lemma

Limits.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins);
    the two earlier chains' starts and walks return; `hm`: the state's field holds the two chains'
    columns (`laid_field` pays it at the state as `ChainProgress.start` lays it): `tie_second`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedStart
import Johnson.Desc.ProofFile.Honest.WalkHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 The field as `ChainProgress.start` lays it -/

theorem laid_field {S W Y : Type} {mo : Option (Mid W Y)} {v : Option S} {front : List OpenedColumn} :
    ∀ m, (if v.isSome then mo.map ({ · with opened := some front }) else none) = some m →
      m.opened = some front := by
  intro m h
  split at h
  · cases mo with
    | none => cases h
    | some m₀ =>
      obtain rfl : ({ m₀ with opened := some front } : Mid W Y) = m := Option.some.inj h
      rfl
  · cases h

/-! ## 2 The two earlier chains' columns -/

/-- **The columns that the first and the shared chain have read are found in what these two chains
have produced.** `q₀`, `q₁`: what they have read; `hq`: each read has words, as in `RunOk.words`
(Honest/Law/Rule/Reads.lean), with no round of the second chain (its first conjunct is not used). -/
theorem held_two {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)}
    {l₀ l₁ : List Played} {q₀ q₁ : List Read} {c₀ c₁ : List OpenedColumn}
    (b₀ : q₀.map Read.bare = (bareReads F ρ).1) (b₁ : q₁.map Read.bare = (bareReads F ρ).2.1)
    (hq : ∀ q ∈ q₀ ++ q₁, q.words.isSome = true ∧
      ((∃ i, q.item = some i ∧ q.src = none ∧ q.words = stored i q.pos) ∨
        ∃ c j T, q.item = none ∧ q.src = some (c, j) ∧ c ≤ 2 ∧
          ((allTabs (pick3 l₀ l₁ [] c))[j]?).join = some T ∧ q.words = some (T.col q.pos)))
    (f₀ : fillCols q₀ [] = .ok c₀) (f₁ : fillCols q₁ [] = .ok c₁) :
    colsOff ((laidOf F ρ l₀ l₁ []).front 2 (storedShown stored (storedAsks F ρ)))
        (bareReads F ρ).1 = some c₀ ∧
      colsOff ((laidOf F ρ l₀ l₁ []).front 2 (storedShown stored (storedAsks F ρ)))
        (bareReads F ρ).2.1 = some c₁ := by
  have hw : ∀ q ∈ q₀ ++ q₁, ∀ w, q.words = some w →
      ((laidOf F ρ l₀ l₁ []).front 2 (storedShown stored (storedAsks F ρ))).wordsAt q.bare =
        some w := by
    intro q hq' w hqw
    have hb : q.bare ∈ allBare F ρ := by
      have hm : q.bare ∈ (q₀ ++ q₁).map Read.bare := List.mem_map.2 ⟨q, hq', rfl⟩
      rw [List.map_append, b₀, b₁] at hm
      show q.bare ∈ (bareReads F ρ).1 ++ (bareReads F ρ).2.1 ++ (bareReads F ρ).2.2
      exact List.mem_append.2 (Or.inl hm)
    obtain ⟨-, hform⟩ := hq q hq'
    rcases hform with ⟨i, g1, -, g3⟩ | ⟨c, j, T, g1, g2, g3, g4, g5⟩
    · have hi : q.bare.item = some i := g1
      unfold Before.wordsAt
      rw [hi]
      show (((storedShown stored (storedAsks F ρ)).find? fun c =>
        c.1 == i && c.2.1 == q.pos).map (·.2.2)) = some w
      exact find_stored stored i q.pos w (g3.symm.trans hqw) _ (mem_storedAsks F ρ q.bare hb i hi)
    · have hi : q.bare.item = none := g1
      have hs : q.bare.src = some (c, j) := g2
      have hcols := treeCols_at F ρ l₀ l₁ [] (storedShown stored (storedAsks F ρ)) c j g3
      have hget : (allTabs (pick3 l₀ l₁ [] c))[j]? = some (some T) := by
        cases hg : (allTabs (pick3 l₀ l₁ [] c))[j]? with
        | none =>
          rw [hg] at g4
          cases g4
        | some t =>
          rw [hg] at g4
          exact congrArg some g4
      rw [hget] at hcols
      have hwT : w = T.col q.pos := Option.some.inj (hqw.symm.trans g5)
      unfold Before.wordsAt
      rw [hi, hs]
      show ((((laidOf F ρ l₀ l₁ []).front 2 (storedShown stored (storedAsks F ρ))).treeCols c
        j).bind fun cols => (cols.find? fun c => c.1 == q.pos).map (·.2)) = some w
      rw [hcols, hwT]
      exact find_col T q.pos _ (mem_treeAsks F ρ q.bare hb _ _ hs)
  have k₀ := colsOff_fill _ q₀ c₀ f₀ fun q h => hw q (List.mem_append.2 (Or.inl h))
  have k₁ := colsOff_fill _ q₁ c₁ f₁ fun q h => hw q (List.mem_append.2 (Or.inr h))
  rw [b₀] at k₀
  rw [b₁] at k₁
  exact ⟨k₀, k₁⟩

/-! ## 3 Before the second chain's first sub-protocol -/

/-- **`TieAt` before the second chain's first sub-protocol.** `hm`: the state's field holds the
columns of the two earlier chains, as `ChainProgress.start` lays them (`laid_field`). -/
theorem tie_second {F : FileDescription Xi} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    {a₁ z₁ : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X} {a₂ z₂ : ChainProgress F.S₂ F.Cl (Common W₀ Rc Ky) X₀}
    {m₁ : Option (Mid (Local W₀ Rc Xi Tr) X)} {m₂ : Option (Mid (Common W₀ Rc Ky) X₀)}
    {v₁ : Option F.S₁} {v₂ : Option F.S₂}
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (ha₁ : ChainProgress.start ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder m₁ v₁ [] = .ok a₁)
    (hz₁ : walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁ = .ok z₁)
    (ha₂ : ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder m₂ v₂ [] = .ok a₂)
    (hz₂ : walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ = .ok z₂)
    {W Y : Type} {mid : Option (Mid W Y)}
    (hm : ∀ m, mid = some m → m.opened = some (z₁.cols ++ z₂.cols)) :
    TieAt (earlierOf F 2) 2 F.lastChainFirstTreeNumber [] mid
      ((laidOf F ρ z₁.laid z₂.laid []).front 2
        (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))) := by
  obtain ⟨-, tr, -, -, -, hs₁, hs₂, -⟩ := ready_ok hR
  have l1 := chainSteps_length _ _ hs₁
  have l2 := chainSteps_length _ _ hs₂
  have C1 := chained_of_start ha₁ hz₁ l1
  have C2 := chained_of_start ha₂ hz₂ l2
  obtain ⟨b1, w1⟩ := words_of C1 rfl l1 (walk_length _ _ _ _ hz₁) z₁.laid z₂.laid []
    fun a b o pT e h => by
      obtain ⟨n, rfl, hn⟩ := own_tab a o pT h
      refine ⟨(show (0 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs z₁.laid)[n]?).join = some pT.2
      have e' : z₁.laid = a ++ b := e
      rw [e']
      exact tabs_prefix a b n pT.2 hn
  obtain ⟨b2, w2⟩ := words_of C2 rfl l2 (walk_length _ _ _ _ hz₂) z₁.laid z₂.laid []
    fun a b o pT e h => by
      obtain ⟨n, rfl, hn⟩ := own_tab a o pT h
      refine ⟨(show (1 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs z₂.laid)[n]?).join = some pT.2
      have e' : z₂.laid = a ++ b := e
      rw [e']
      exact tabs_prefix a b n pT.2 hn
  obtain ⟨r1, c1, f1, g1, k1⟩ := chained_cols _ _ _ _ _ C1
  obtain ⟨r2, c2, f2, g2, k2⟩ := chained_cols _ _ _ _ _ C2
  have F1 : fillCols z₁.reads [] = .ok z₁.cols := by
    have e1 : z₁.reads = r1 := f1
    have e2 : z₁.cols = c1 := g1
    rw [e1, e2]
    exact k1
  have F2 : fillCols z₂.reads [] = .ok z₂.cols := by
    have e1 : z₂.reads = r2 := f2
    have e2 : z₂.cols = c2 := g2
    rw [e1, e2]
    exact k2
  obtain ⟨h₁, h₂⟩ := held_two (F := F) (ρ := ρ) (stored := P.storedWords w₀ rc) (l₀ := z₁.laid)
    (l₁ := z₂.laid) (q₀ := z₁.reads) (q₁ := z₂.reads) b1 b2
    (fun q hq => by
      rcases List.mem_append.1 hq with h | h
      · exact w1 q h
      · exact w2 q h) F1 F2
  have d0 : ((laidOf F ρ z₁.laid z₂.laid []).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))).drawnOf 0 = ρ.first := by
    rw [drawnOf_laid F ρ z₁.laid z₂.laid [] _ 0 (by decide)]
    have e := walk_laid_drawn _ _ _ a₁ z₁ hz₁
    rw [start_laid ha₁, List.map_nil, List.nil_append] at e
    exact e
  have d1 : ((laidOf F ρ z₁.laid z₂.laid []).front 2
      (storedShown (P.storedWords w₀ rc) (storedAsks F ρ))).drawnOf 1 = ρ.shared := by
    rw [drawnOf_laid F ρ z₁.laid z₂.laid [] _ 1 (by decide)]
    have e := walk_laid_drawn _ _ _ a₂ z₂ hz₂
    rw [start_laid ha₂, List.map_nil, List.nil_append] at e
    exact e
  have n1 : F.roundsDeclaredByBlocks.1.length = ρ.first.length := by
    have e := congrArg List.length (steps_decl hs₁)
    rw [List.length_map] at e
    exact (((walk_length _ _ _ _ hz₁).trans e)).symm
  have n2 : F.roundsDeclaredByBlocks.2.1.length = ρ.shared.length := by
    have e := congrArg List.length (steps_decl hs₂)
    rw [List.length_map] at e
    exact (((walk_length _ _ _ _ hz₂).trans e)).symm
  show TieAt [(0, 0, F.roundsDeclaredByBlocks.1), (1, 0, F.roundsDeclaredByBlocks.2.1)] 2 F.lastChainFirstTreeNumber [] mid _
  refine TieAt.start₃ hm ?_ ?_ ?_ ?_ ?_
  · rw [d0]
    exact h₁
  · rw [d1]
    exact h₂
  · rw [d0]
    exact Nat.le_of_eq n1
  · rw [d1]
    exact Nat.le_of_eq n2
  · exact drawnOf_laid F ρ z₁.laid z₂.laid [] _ 2 (by decide)

end ProofFile.Honest

#print axioms ProofFile.Honest.laid_field
#print axioms ProofFile.Honest.held_two
#print axioms ProofFile.Honest.tie_second
