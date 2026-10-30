-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/FaithOwnFile.lean: `FaithOwn`
(Honest/Law/Rule/OpenedStep.lean) at each of a description's three chains, beside `faithAll_of`
(Honest/Law/Rule/FaithFile.lean), from that lemma's hypotheses and one more: a tree that the look-up
of the first or the shared chain returns is the chain's own (`hsrc`; paid, with the others, in
Honest/Law/Rule/Model.lean and Honest/Law/Rule/FileInv.lean). No coin, no part and no run of a
protocol occurs here.

  1  `Laid.front_stored`, `treeCols_own`, `wordsAt_own`   what three chains' rounds show
     (`laidOf`, Honest/Law/Rule/Words.lean): for a read of a stored table, and for a read of a tree
     that the chain itself has sent, the cut for the chain holds the words that the cut for the
     second chain holds
  2  `faithOwn_of`   one chain

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.FaithFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

variable {Xi S Cl : Type}

/-! ## 1 The cut for the chain, and the cut for the second chain -/

theorem Laid.front_stored (L : Laid) (ch : Nat) (st : List (Nat × Nat × List UInt64)) :
    (L.front ch st).stored = st := by
  unfold Laid.front
  by_cases h0 : (ch == 0) = true
  · simp [h0]
  · by_cases h1 : (ch == 1) = true
    · simp [h0, h1]
    · simp [h0, h1]

/-- `treeCols_at` (Honest/Law/Rule/Words.lean) in the cut for chain number `ch`: of the chain's own
trees; from 2 on of all three chains'. It is `treeCols_front` (Honest/Law/Rule/Holds.lean) with `2 ≤
ch` for `ch = 2`. -/
theorem treeCols_own (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (Nat × Nat × List UInt64)) (ch c j : Nat) (hc : c ≤ 2) (h : ch = c ∨ 2 ≤ ch) :
    ((laidOf F ρ l₀ l₁ l₂).front ch st).treeCols c j =
      ((allTabs (pick3 l₀ l₁ l₂ c))[j]?).map fun T => colsOfT T (treeAsks F ρ c j) := by
  have h0 : ∀ (t : Nat → List Nat) (l : List Played),
      ((shownBy c t l 0).flatMap (·.2.1.cols))[j]? =
        ((allTabs l)[j]?).map fun T => colsOfT T (t j) := by
    intro t l
    have := cols_at c t l 0 j
    rw [Nat.zero_add] at this
    exact this
  by_cases e0 : ch = 0
  · subst e0
    have hc0 : c = 0 := by omega
    subst hc0
    show (((shownBy 0 (treeAsks F ρ 0) l₀ 0).filter fun r => r.1 == 0).flatMap
      fun r => r.2.1.cols)[j]? = _
    rw [filter_same]
    exact h0 _ _
  · by_cases e1 : ch = 1
    · subst e1
      have hc1 : c = 1 := by omega
      subst hc1
      show (((shownBy 1 (treeAsks F ρ 1) l₁ 0).filter fun r => r.1 == 1).flatMap
        fun r => r.2.1.cols)[j]? = _
      rw [filter_same]
      exact h0 _ _
    · have e : (laidOf F ρ l₀ l₁ l₂).front ch st = (laidOf F ρ l₀ l₁ l₂).front 2 st := by
        unfold Laid.front
        simp [e0, e1]
      rw [e]
      exact treeCols_at F ρ l₀ l₁ l₂ st c j hc

/-- `h`: a read of a tree reads one of the chain's own; from chain number 2 on: of any of the three.
-/
theorem wordsAt_own (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (Nat × Nat × List UInt64)) (ch : Nat) (q : Read)
    (h : ∀ c j, q.item = none → q.src = some (c, j) → c ≤ 2 ∧ (ch = c ∨ 2 ≤ ch)) :
    ((laidOf F ρ l₀ l₁ l₂).front ch st).wordsAt q =
      ((laidOf F ρ l₀ l₁ l₂).front 2 st).wordsAt q := by
  unfold Before.wordsAt
  cases hi : q.item with
  | some i =>
    show ((((laidOf F ρ l₀ l₁ l₂).front ch st).stored.find? fun c =>
        c.1 == i && c.2.1 == q.pos).map (·.2.2)) =
      ((((laidOf F ρ l₀ l₁ l₂).front 2 st).stored.find? fun c =>
        c.1 == i && c.2.1 == q.pos).map (·.2.2))
    rw [Laid.front_stored, Laid.front_stored]
  | none =>
    cases hs : q.src with
    | none => rfl
    | some p =>
      obtain ⟨c, j⟩ := p
      obtain ⟨hc, hch⟩ := h c j hi hs
      show ((((laidOf F ρ l₀ l₁ l₂).front ch st).treeCols c j).bind fun cols =>
          (cols.find? fun z => z.1 == q.pos).map (·.2)) =
        ((((laidOf F ρ l₀ l₁ l₂).front 2 st).treeCols c j).bind fun cols =>
          (cols.find? fun z => z.1 == q.pos).map (·.2))
      rw [treeCols_own F ρ l₀ l₁ l₂ st ch c j hc hch, treeCols_at F ρ l₀ l₁ l₂ st c j hc]

/-! ## 2 One chain -/

/-- **`FaithOwn` at one chain.** The letters and the first hypotheses are those of `faithAll_of`.
`hsrc`: a tree that is available to the chain's reads is the chain's own; from chain number 2 on
nothing is asked. -/
theorem faithOwn_of (F : FileDescription Xi) (ρ : Draws) (ch ft : Nat) (L : Lay) (Z₀ : Laid)
    (trip : List Played → List Played × List Played × List Played)
    (hZ : ∀ l, Z₀.add ch (pairsBy (treeAsks F ρ ch) l 0) =
      laidOf F ρ (trip l).1 (trip l).2.1 (trip l).2.2)
    (htr : ∀ l o pT, L.tree l o = some pT → (srcOf ch o).1 ≤ 2 ∧
      ((allTabs (pick3 (trip l).1 (trip l).2.1 (trip l).2.2
        (srcOf ch o).1))[(srcOf ch o).2]?).join = some pT.2)
    (hsrc : ∀ l o pT, L.tree l o = some pT → ch = (srcOf ch o).1 ∨ 2 ≤ ch) :
    ∀ (bs : List (Block S Cl)) (ds : List Fmt.Drawn), ds.length = (bs.map (·.rounds.length)).sum →
    (∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) ds,
      q ∈ allBare F ρ) →
    FaithOwn ch ft (storedShown L.stored (storedAsks F ρ)) (treeAsks F ρ ch) L Z₀ bs ds
  | [], _, _, _ => trivial
  | b :: bs, ds, hl, hm => by
    have hall := faithAll_of F ρ ch ft L Z₀ trip hZ htr (b :: bs) ds hl hm
    rw [FaithAll] at hall
    simp only [List.map_cons, List.sum_cons] at hl
    have htl : b.rounds.length = (ds.take b.rounds.length).length := by
      rw [List.length_take]
      omega
    have hsplit : readsOf ch ft (fun _ _ => none) (fun _ => none)
        ((b :: bs).flatMap (·.rounds)) ds =
        readsOf ch ft (fun _ _ => none) (fun _ => none) b.rounds (ds.take b.rounds.length) ++
          readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds))
            (ds.drop b.rounds.length) := by
      rw [List.flatMap_cons]
      conv_lhs => rw [← List.take_append_drop b.rounds.length ds]
      exact readsOf_append _ _ _ _ _ _ _ _ htl
    rw [hsplit] at hm
    rw [FaithOwn]
    refine ⟨fun l q hq w hw => ?_, faithOwn_of F ρ ch ft L Z₀ trip hZ htr hsrc bs _
      (by rw [List.length_drop]; omega) fun q hq => hm q (List.mem_append.2 (Or.inr hq))⟩
    have h2 := hall.1 l q hq w hw
    rw [hZ l] at h2 ⊢
    have hside : ∀ c j, q.bare.item = none → q.bare.src = some (c, j) →
        c ≤ 2 ∧ (ch = c ∨ 2 ≤ ch) := by
      intro c j hi hs
      rcases readsOf_form ch ft L.stored (L.tree l) b.rounds _ q hq with
        ⟨i, h1, -, -⟩ | ⟨o, -, g2, g3⟩
      · have hi' : q.item = none := hi
        rw [h1] at hi'
        cases hi'
      · have hs' : q.src = some (c, j) := hs
        rw [g2] at hs'
        have ec : (srcOf ch o).1 = c := congrArg Prod.fst (Option.some.inj hs')
        rw [hw] at g3
        cases hto : L.tree l o with
        | none =>
          rw [hto] at g3
          cases g3
        | some pT =>
          rw [← ec]
          exact ⟨(htr l o pT hto).1, hsrc l o pT hto⟩
    rw [wordsAt_own F ρ _ _ _ _ ch q.bare hside]
    exact h2

end ProofFile.Honest

#print axioms ProofFile.Honest.Laid.front_stored
#print axioms ProofFile.Honest.treeCols_own
#print axioms ProofFile.Honest.wordsAt_own
#print axioms ProofFile.Honest.faithOwn_of
