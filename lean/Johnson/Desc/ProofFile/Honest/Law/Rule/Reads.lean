-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Reads.lean: what a run of the prover of Honest/Walk.lean
shows (Honest/Law/Rule/Session.lean: `Run.laid`) is what its rounds show at the positions that the
description's declared rounds read (Honest/Law/Rule/Words.lean: `laidOf`): this is `laid_is`. And
the three views that a session computes from that (`viewsOff`) are the run's own (`views_back`).

  1  `chained_cols`   a chain's columns are those that `fillCols` fills for all that its
     sub-protocols have read
  2  `RunOk`, `RunOk.bare`, `words_of`, `runOk_of`   what the two lemmas use of a run, as one
     proposition; a run that goes through satisfies it
  3  `shown_is`, `laid_is`   what the run shows
  4  `views_back`   the three views

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainEnd
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainFile
import Johnson.Desc.ProofFile.Honest.Law.Rule.FaithFile
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 A chain's columns -/

theorem chained_cols {S Cl W Y : Type} {L : Lay} :
    ∀ (bs : List (Block S Cl)) (ss : List (Step W Y)) (ds : List Fmt.Drawn) (c c' : Core S W Y),
    Chained L bs ss ds c c' → ∃ nr nc, c'.reads = c.reads ++ nr ∧ c'.cols = c.cols ++ nc ∧
      fillCols nr [] = .ok nc
  | [], ss, ds, c, c', hC => by
    rw [Chained] at hC
    obtain ⟨-, -, rfl⟩ := hC
    exact ⟨[], [], (List.append_nil _).symm, (List.append_nil _).symm, rfl⟩
  | b :: bs, ss, ds, c, c', hC => by
    rw [Chained] at hC
    obtain ⟨y, cols, -, hc, hC'⟩ := hC
    obtain ⟨nr, nc, h1, h2, h3⟩ := chained_cols bs _ _ _ _ hC'
    refine ⟨readsOf L.chain L.firstTree L.stored (L.tree (c.laid ++ y.1)) b.rounds
      (y.1.map (·.drawn)) ++ nr, cols ++ nc, ?_, ?_, ?_⟩
    · rw [h1]
      exact List.append_assoc _ _ _
    · rw [h2]
      exact List.append_assoc _ _ _
    · rw [fillCols_append, hc]
      show ((fillCols nr (([] : List OpenedColumn).drop _)).map fun c₂ => cols ++ c₂) = _
      rw [List.drop_nil, h3]
      rfl

/-! ## 2 What the two lemmas use of a run -/

/-- **What `laid_is` and `views_back` use of a run, as one proposition.** `l₀`, `l₁`, `l₂`: the
three chains' rounds. `q₀`, `q₁`, `q₂`: what they have read. `stored`: the stored tables' columns,
by item and position. `bare₀`, `bare₁`, `bare₂`: each chain's reads, with sender and words taken off
(`Read.bare`), are those that the description's declared rounds make at these challenges
(`bareReads`). -/
structure RunOk (F : FileDescription Xi) (ρ : Draws) (stored : Nat → Nat → Option (List UInt64))
    (l₀ l₁ l₂ : List Played) (q₀ q₁ q₂ : List Read) : Prop where
  bare₀ : q₀.map Read.bare = (bareReads F ρ).1
  bare₁ : q₁.map Read.bare = (bareReads F ρ).2.1
  bare₂ : q₂.map Read.bare = (bareReads F ρ).2.2
  /-- each read has words: a stored table's column; or the column of the table of its source's
  number among the rounds of the chain that sent it -/
  words : ∀ q ∈ q₀ ++ q₁ ++ q₂, q.words.isSome = true ∧
    ((∃ i, q.item = some i ∧ q.src = none ∧ q.words = stored i q.pos) ∨
      ∃ c j T, q.item = none ∧ q.src = some (c, j) ∧ c ≤ 2 ∧
        ((allTabs (pick3 l₀ l₁ l₂ c))[j]?).join = some T ∧ q.words = some (T.col q.pos))

theorem RunOk.bare {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)}
    {l₀ l₁ l₂ : List Played} {q₀ q₁ q₂ : List Read} (h : RunOk F ρ stored l₀ l₁ l₂ q₀ q₁ q₂) :
    (q₀ ++ q₁ ++ q₂).map Read.bare = allBare F ρ := by
  rw [List.map_append, List.map_append, h.bare₀, h.bare₁, h.bare₂]
  rfl

/-- One chain's reads satisfy the condition on words. `tab`: the hypothesis on the table behind a
source, at every stretch of the chain's rounds from its start. -/
theorem words_of {S Cl W Y : Type} {L : Lay} {bs : List (Block S Cl)} {ss : List (Step W Y)}
    {ds : List Fmt.Drawn} {c c' : Core S W Y} (hC : Chained L bs ss ds c c') (hr : c.reads = [])
    (hl : ss.length = (bs.map (·.rounds.length)).sum) (hd : ds.length = ss.length)
    (l₀ l₁ l₂ : List Played)
    (tab : ∀ a b o pT, c'.laid = a ++ b → L.tree a o = some pT → (srcOf L.chain o).1 ≤ 2 ∧
      ((allTabs (pick3 l₀ l₁ l₂ (srcOf L.chain o).1))[(srcOf L.chain o).2]?).join = some pT.2) :
    c'.reads.map Read.bare = readsOf L.chain L.firstTree (fun _ _ => none) (fun _ => none)
        (bs.flatMap (·.rounds)) ds ∧
      ∀ q ∈ c'.reads, q.words.isSome = true ∧
        ((∃ i, q.item = some i ∧ q.src = none ∧ q.words = L.stored i q.pos) ∨
          ∃ c j T, q.item = none ∧ q.src = some (c, j) ∧ c ≤ 2 ∧
            ((allTabs (pick3 l₀ l₁ l₂ c))[j]?).join = some T ∧ q.words = some (T.col q.pos)) := by
  obtain ⟨new, h1, h2, h3⟩ := chained_reads bs ss ds c c' hC hl hd
  rw [hr, List.nil_append] at h1
  rw [h1]
  refine ⟨h2, fun q hq => ?_⟩
  obtain ⟨w1, a, b, blk, own, e1, -, e3⟩ := h3 q hq
  refine ⟨w1, ?_⟩
  rcases readsOf_form _ _ _ _ _ _ q e3 with ⟨i, g1, g2, g3⟩ | ⟨o, g1, g2, g3⟩
  · exact Or.inl ⟨i, g1, g2, g3⟩
  · cases ht : L.tree a o with
    | none =>
      rw [g3, ht] at w1
      cases w1
    | some pT =>
      obtain ⟨t1, t2⟩ := tab a b o pT e1 ht
      refine Or.inr ⟨(srcOf L.chain o).1, (srcOf L.chain o).2, pT.2, g1, g2, t1, t2, ?_⟩
      rw [g3, ht]
      rfl

/-- **A run that goes through satisfies `RunOk`.** And each view's columns are what `fillCols` fills
for its chain's reads. -/
theorem runOk_of {F : FileDescription Xi} {Bk : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {k : Coins Bk} {ρ : Draws} {r : RunC F} (hrun : runC F Bk P w₀ rc x k ρ = .ok r) :
    RunOk F ρ (P.storedWords w₀ rc) r.run.played.1 r.run.played.2.1 r.run.played.2.2 r.run.reads.1
        r.run.reads.2.1 r.run.reads.2.2 ∧
      fillCols r.run.reads.1 [] = .ok r.run.views.1.opened ∧
      fillCols r.run.reads.2.1 [] = .ok r.run.views.2.1.opened ∧
      fillCols r.run.reads.2.2 [] = .ok r.run.views.2.2.opened := by
  obtain ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, -, ha₂, hz₂, ha₃, hz₃, rfl⟩ := runC_parts hrun
  obtain ⟨-, tr, -, -, -, hs₁, hs₂, hs₃⟩ := ready_ok hR
  have l1 := chainSteps_length _ _ hs₁
  have l2 := chainSteps_length _ _ hs₂
  have l3 := chainSteps_length _ _ hs₃
  have C1 := chained_of_start ha₁ hz₁ l1
  have C2 := chained_of_start ha₂ hz₂ l2
  have C3 := chained_of_start ha₃ hz₃ l3
  obtain ⟨b1, w1⟩ := words_of C1 rfl l1 (walk_length _ _ _ _ hz₁) z₁.laid z₂.laid z₃.laid
    fun a b o pT e h => by
      obtain ⟨n, rfl, hn⟩ := own_tab a o pT h
      refine ⟨(show (0 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs z₁.laid)[n]?).join = some pT.2
      have e' : z₁.laid = a ++ b := e
      rw [e']
      exact tabs_prefix a b n pT.2 hn
  obtain ⟨b2, w2⟩ := words_of C2 rfl l2 (walk_length _ _ _ _ hz₂) z₁.laid z₂.laid z₃.laid
    fun a b o pT e h => by
      obtain ⟨n, rfl, hn⟩ := own_tab a o pT h
      refine ⟨(show (1 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs z₂.laid)[n]?).join = some pT.2
      have e' : z₂.laid = a ++ b := e
      rw [e']
      exact tabs_prefix a b n pT.2 hn
  obtain ⟨b3, w3⟩ := words_of C3 rfl l3 (walk_length _ _ _ _ hz₃) z₁.laid z₂.laid z₃.laid
    fun a b o pT e h => by
      have e' : z₃.laid = a ++ b := e
      obtain ⟨t1, t2⟩ := third_tab z₁.laid z₂.laid a o pT h
      refine ⟨t1, ?_⟩
      cases o with
      | own n =>
        show ((allTabs z₃.laid)[n]?).join = some pT.2
        rw [e']
        exact tabs_prefix a b n pT.2 t2
      | taken cc kk =>
        have hc : cc ≤ 2 := t1
        have hc3 : cc = 0 ∨ cc = 1 ∨ cc = 2 := by omega
        rcases hc3 with rfl | rfl | rfl
        · exact t2
        · exact t2
        · have t2' : ((allTabs a)[kk]?).join = some pT.2 := t2
          show ((allTabs z₃.laid)[kk]?).join = some pT.2
          rw [e']
          exact tabs_prefix a b kk pT.2 t2'
  obtain ⟨r1, c1, f1, g1, k1⟩ := chained_cols _ _ _ _ _ C1
  obtain ⟨r2, c2, f2, g2, k2⟩ := chained_cols _ _ _ _ _ C2
  obtain ⟨r3, c3, f3, g3, k3⟩ := chained_cols _ _ _ _ _ C3
  refine ⟨⟨b1, b2, b3, fun q hq => ?_⟩, ?_, ?_, ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · rcases List.mem_append.1 hq with hq | hq
      · exact w1 q hq
      · exact w2 q hq
    · exact w3 q hq
  · show fillCols z₁.reads [] = .ok z₁.cols
    have e1 : z₁.reads = r1 := f1
    have e2 : z₁.cols = c1 := g1
    rw [e1, e2]
    exact k1
  · show fillCols z₂.reads [] = .ok z₂.cols
    have e1 : z₂.reads = r2 := f2
    have e2 : z₂.cols = c2 := g2
    rw [e1, e2]
    exact k2
  · show fillCols z₃.reads [] = .ok z₃.cols
    have e1 : z₃.reads = r3 := f3
    have e2 : z₃.cols = c3 := g3
    rw [e1, e2]
    exact k3

/-! ## 3 What the run shows -/

section
variable {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)}
  {l₀ l₁ l₂ : List Played} {q₀ q₁ q₂ : List Read}

/-- One chain's rounds. -/
theorem shown_is (h : RunOk F ρ stored l₀ l₁ l₂ q₀ q₁ q₂) (c : Nat) (hc : c ≤ 2) :
    ((shownIn c (pick3 l₀ l₁ l₂ c) (q₀ ++ q₁ ++ q₂)).map fun y => (c, y.2, y.1.drawn)) =
      shownBy c (treeAsks F ρ c) (pick3 l₀ l₁ l₂ c) 0 := by
  have key := shownIn_by c (treeAsks F ρ c) (q₀ ++ q₁ ++ q₂) (pick3 l₀ l₁ l₂ c) 0
    fun a p b hl i hi => by
      rw [Nat.zero_add]
      have hT := allTabs_at a p b i hi
      rw [← hl] at hT
      rw [← hT]
      refine cols_by F ρ _ h.bare c _ _ fun q hq hs => ?_
      obtain ⟨w1, hw⟩ := h.words q hq
      refine ⟨w1, ?_⟩
      rcases hw with ⟨i', -, g2, -⟩ | ⟨c', j', T, -, g2, -, g4, g5⟩
      · rw [g2] at hs
        cases hs
      · rw [g2] at hs
        have e := Option.some.inj hs
        have e1 : c' = c := congrArg (·.1) e
        have e2 : j' = (a.map (·.tables.length)).sum + i := congrArg (·.2) e
        subst e1
        subst e2
        rw [g4, g5]
        rfl
  rw [← key]
  unfold shownIn
  rw [List.map_map]
  rfl

end

/-- **What a run shows is what its rounds show at the positions read.** -/
theorem laid_is {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)} (r : Run)
    (h : RunOk F ρ stored r.played.1 r.played.2.1 r.played.2.2 r.reads.1 r.reads.2.1 r.reads.2.2) :
    r.laid = laidOf F ρ r.played.1 r.played.2.1 r.played.2.2 := by
  have h0 := shown_is h 0 (by decide)
  have h1 := shown_is h 1 (by decide)
  have h2 := shown_is h 2 (by decide)
  unfold Run.laid laidOf
  exact congr (congr (congrArg Laid.mk h0) h1) h2

/-! ## 4 The three views -/

/-- **The three views that a session computes from what a run shows are the run's own** (written
out: each chain's rounds as a view shows them, the first chain's without its last round, and the
columns that `fillCols` fills). -/
theorem views_back {F : FileDescription Xi} {ρ : Draws} {stored : Nat → Nat → Option (List UInt64)}
    {l₀ l₁ l₂ : List Played} {q₀ q₁ q₂ : List Read} {c₀ c₁ c₂ : List OpenedColumn}
    (h : RunOk F ρ stored l₀ l₁ l₂ q₀ q₁ q₂) (f₀ : fillCols q₀ [] = .ok c₀)
    (f₁ : fillCols q₁ [] = .ok c₁) (f₂ : fillCols q₂ [] = .ok c₂) :
    viewsOff F ρ (storedShown stored (storedAsks F ρ)) (laidOf F ρ l₀ l₁ l₂) =
      some (⟨(roundsOf l₀).dropLast, c₀⟩, ⟨roundsOf l₁, c₁⟩, ⟨roundsOf l₂, c₂⟩) := by
  have hw : ∀ q ∈ q₀ ++ q₁ ++ q₂, ∀ w, q.words = some w →
      ((laidOf F ρ l₀ l₁ l₂).front 2 (storedShown stored (storedAsks F ρ))).wordsAt q.bare =
        some w := by
    intro q hq w hqw
    have hb : q.bare ∈ allBare F ρ := by
      rw [← h.bare]
      exact List.mem_map.2 ⟨q, hq, rfl⟩
    obtain ⟨-, hform⟩ := h.words q hq
    rcases hform with ⟨i, g1, -, g3⟩ | ⟨c, j, T, g1, g2, g3, g4, g5⟩
    · have hi : q.bare.item = some i := g1
      unfold Before.wordsAt
      rw [hi]
      show (((storedShown stored (storedAsks F ρ)).find? fun c =>
        c.1 == i && c.2.1 == q.pos).map (·.2.2)) = some w
      exact find_stored stored i q.pos w (g3.symm.trans hqw) _ (mem_storedAsks F ρ q.bare hb i hi)
    · have hi : q.bare.item = none := g1
      have hs : q.bare.src = some (c, j) := g2
      have hcols := treeCols_at F ρ l₀ l₁ l₂ (storedShown stored (storedAsks F ρ)) c j g3
      have hget : (allTabs (pick3 l₀ l₁ l₂ c))[j]? = some (some T) := by
        cases hg : (allTabs (pick3 l₀ l₁ l₂ c))[j]? with
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
      show ((((laidOf F ρ l₀ l₁ l₂).front 2 (storedShown stored (storedAsks F ρ))).treeCols c
        j).bind fun cols => (cols.find? fun c => c.1 == q.pos).map (·.2)) = some w
      rw [hcols, hwT]
      exact find_col T q.pos _ (mem_treeAsks F ρ q.bare hb _ _ hs)
  have k₀ := colsOff_fill _ q₀ c₀ f₀ fun q hq =>
    hw q (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl hq))))
  have k₁ := colsOff_fill _ q₁ c₁ f₁ fun q hq =>
    hw q (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hq))))
  have k₂ := colsOff_fill _ q₂ c₂ f₂ fun q hq => hw q (List.mem_append.2 (Or.inr hq))
  rw [h.bare₀] at k₀
  rw [h.bare₁] at k₁
  rw [h.bare₂] at k₂
  unfold viewsOff
  rw [k₀, k₁, k₂]
  show some ((⟨(roundsOff (shownBy 0 (treeAsks F ρ 0) l₀ 0)).dropLast, c₀⟩ : Fmt.View),
    (⟨roundsOff (shownBy 1 (treeAsks F ρ 1) l₁ 0), c₁⟩ : Fmt.View),
    (⟨roundsOff (shownBy 2 (treeAsks F ρ 2) l₂ 0), c₂⟩ : Fmt.View)) = _
  rw [roundsOff_by, roundsOff_by, roundsOff_by]

end ProofFile.Honest

#print axioms ProofFile.Honest.chained_cols
#print axioms ProofFile.Honest.RunOk.bare
#print axioms ProofFile.Honest.words_of
#print axioms ProofFile.Honest.runOk_of
#print axioms ProofFile.Honest.shown_is
#print axioms ProofFile.Honest.laid_is
#print axioms ProofFile.Honest.views_back
#print axioms ProofFile.Honest.RunOk
