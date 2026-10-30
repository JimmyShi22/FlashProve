-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ReadsOfTree.lean: the frame's list of the positions that are read
of one tree, in any round of a file's three chains (`treeAsks`,
Johnson/Desc/ProofFile/Honest/Law/Rule/Bare.lean), held against the openings that the description's
declared rounds state. General in the description, the chain and the tree's number. Counting lemmas
on public data: no input, no random value, no run. It imports Mathlib.

  `openedOf`, `openedAll`   the openings that declared rounds state, one chain's and all three's:
                 for each the tree's source (the chain that sent it; its number there), the number
                 of positions that the opening round samples, and the depth that the opening states
  `length_listOf`, `mem_listOf`   `Fmt.listOf` (Fmt/Rules6.lean) is no longer than its list and has
                 no other member
  `reads_len`, `reads_pos`   one chain: the reads whose source is s are no more than the positions
                 of the openings of s, added up; each such read's position lies below 2 ^ a for an
                 opening of s that states the depth a
  `asks_len`, `asks_pos`   the same of `treeAsks`, at every list of challenges that passes
                 `Draws.due` (Johnson/Desc/ProofFile/Honest/Frame.lean)
  `srcs_openings`   the sources in `openedAll` are those of the library's `BookPlan.openings`
                 (Johnson/Desc/BookPlan.lean), in the same order
  `opens_once`   under the library's test `BookPlan.once`: a tree that is told with a tenant that is
                 not sampled has one opening at most, in all three chains together
  `asks_of_one`  so: where such a tree has an opening that samples P positions and states the depth
                 a, `treeAsks` has at most P members, each below 2 ^ a

Limits. "At most": nothing says that a position is read. `treeAsks` is computed of the declared
rounds and the challenges: that a run asks for no position beyond that list is not said here. One
list of challenges: nothing on several requests. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Bare
import Johnson.Desc.BookPlanLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Place Oracle BookPlan.openings BookPlan.once
  BookPlan.DeclaredRoundsByChain BookPlan.SentOraclesByChain)

variable {Xi : Type}

/-! ## 1 The openings -/

/-- One chain's openings: the source, the round's number of positions, the depth stated. c: the
chain's number, from 0. -/
def openedOf (c : ℕ) (ds : List Fmt.DeclaredRound) : List ((ℕ × ℕ) × ℕ × ℕ) :=
  ds.flatMap fun d => d.opens.map fun o => (srcOf c o.2, d.entry.poss, o.1.a)

/-- The three chains'. -/
def openedAll (D : BookPlan.DeclaredRoundsByChain) : List ((ℕ × ℕ) × ℕ × ℕ) :=
  openedOf 0 D.1 ++ openedOf 1 D.2.1 ++ openedOf 2 D.2.2

/-! ## 2 The list of positions -/

theorem length_insertN (x : ℕ) : ∀ l : List ℕ, (Fmt.insertIntoIncreasingList x l).length ≤ l.length + 1
  | [] => Nat.le_refl _
  | y :: l => by
    unfold Fmt.insertIntoIncreasingList
    split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_succ _
      · exact Nat.succ_le_succ (length_insertN x l)

theorem mem_insertN (x z : ℕ) : ∀ l : List ℕ, z ∈ Fmt.insertIntoIncreasingList x l → z = x ∨ z ∈ l
  | [], h => Or.inl (List.mem_singleton.1 h)
  | y :: l, h => by
    unfold Fmt.insertIntoIncreasingList at h
    split at h
    · exact List.mem_cons.1 h
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.1 h with e | e
        · exact Or.inr (e ▸ List.mem_cons_self)
        · rcases mem_insertN x z l e with e' | e'
          · exact Or.inl e'
          · exact Or.inr (List.mem_cons_of_mem _ e')

theorem length_listOf : ∀ l : List ℕ, (Fmt.listOf l).length ≤ l.length
  | [] => Nat.le_refl _
  | x :: l => Nat.le_trans (length_insertN x (Fmt.listOf l)) (Nat.succ_le_succ (length_listOf l))

theorem mem_listOf (z : ℕ) : ∀ l : List ℕ, z ∈ Fmt.listOf l → z ∈ l
  | [], h => h
  | x :: l, h => by
    rcases mem_insertN x z (Fmt.listOf l) h with e | e
    · exact e ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_listOf z l e)

/-! ## 3 One chain -/

section Chain
variable (c ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
  (tree : Fmt.TreeSource → Option (Place × Table)) (s : ℕ × ℕ)

/-- One round's reads of trees, by its openings. -/
theorem opens_len (P : ℕ) (poss : List ℕ) (hP : poss.length = P) :
    ∀ os : List (Fmt.Shape × Fmt.TreeSource),
    ((os.flatMap fun o => (Fmt.listOf (poss.map (· % 2 ^ o.1.a))).map fun x =>
        (⟨o.1.tree - ft, x, none, some (srcOf c o.2), (tree o.2).map (·.1),
          (tree o.2).map (·.2.col x), o.1.W⟩ : Read)).filter fun q => q.src == some s).length ≤
      (((os.map fun o => (srcOf c o.2, P, o.1.a)).filter (·.1 == s)).map (·.2.1)).sum
  | [] => Nat.le_refl _
  | o :: os => by
    have ih := opens_len P poss hP os
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.map_cons]
    by_cases e : srcOf c o.2 = s
    · have h1 : ((srcOf c o.2, P, o.1.a) : (ℕ × ℕ) × ℕ × ℕ).1 == s := by
        show (srcOf c o.2 == s) = true
        rw [e]
        exact beq_self_eq_true _
      rw [List.filter_cons_of_pos (p := fun x : (ℕ × ℕ) × ℕ × ℕ => x.1 == s) h1, List.map_cons,
        List.sum_cons]
      refine Nat.add_le_add (Nat.le_trans (List.length_filter_le _ _) ?_) ih
      rw [List.length_map]
      refine Nat.le_trans (length_listOf _) ?_
      rw [List.length_map, hP]
    · have h1 : ¬ (((srcOf c o.2, P, o.1.a) : (ℕ × ℕ) × ℕ × ℕ).1 == s) = true := by
        intro h
        exact e (beq_iff_eq.1 h)
      rw [List.filter_cons_of_neg (p := fun x : (ℕ × ℕ) × ℕ × ℕ => x.1 == s) h1]
      have h2 : (((Fmt.listOf (poss.map (· % 2 ^ o.1.a))).map fun x =>
          (⟨o.1.tree - ft, x, none, some (srcOf c o.2), (tree o.2).map (·.1),
            (tree o.2).map (·.2.col x), o.1.W⟩ : Read)).filter fun q => q.src == some s) = [] := by
        refine List.filter_eq_nil_iff.2 fun q hq => ?_
        obtain ⟨x, _, rfl⟩ := List.mem_map.1 hq
        intro h
        exact e (Option.some.inj (beq_iff_eq.1 h))
      rw [h2]
      simpa using ih

/-- **The reads whose source is s are no more than the positions of the openings of s.** -/
theorem reads_len : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), drawsFit ds Rs = true →
    ((readsOf c ft stored tree ds Rs).filter fun q => q.src == some s).length ≤
      (((openedOf c ds).filter (·.1 == s)).map (·.2.1)).sum
  | [], _, _ => by simp [readsOf]
  | _ :: _, [], h => by simp [drawsFit] at h
  | d :: ds, R :: Rs, h => by
    have h' : (drawFit d R && drawsFit ds Rs) = true := h
    rw [Bool.and_eq_true] at h'
    have hP : R.poss.length = d.entry.poss := by
      have := h'.1
      unfold drawFit at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      exact this.1.1.1.1.1.1.2
    have ih := reads_len ds Rs h'.2
    have h0 : ((d.stored.flatMap fun t =>
        (Fmt.listOf ((Fmt.partOf t R.poss).map (· % 2 ^ t.sh.a))).map fun x =>
          (⟨Fmt.storedKey t.item, x, some t.item, none, none, stored t.item x, t.sh.W⟩ :
            Read)).filter fun q => q.src == some s) = [] := by
      refine List.filter_eq_nil_iff.2 fun q hq => ?_
      obtain ⟨t, _, hq⟩ := List.mem_flatMap.1 hq
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 hq
      intro h
      cases beq_iff_eq.1 h
    rw [readsOf, List.filter_append, List.filter_append, h0, List.nil_append, List.length_append]
    unfold openedOf
    rw [List.flatMap_cons, List.filter_append, List.map_append, List.sum_append]
    exact Nat.add_le_add (opens_len c ft tree s d.entry.poss R.poss hP d.opens) ih

/-- **A read whose source is s lies below 2 ^ a for an opening of s that states the depth a.** -/
theorem reads_pos : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    ∀ q ∈ readsOf c ft stored tree ds Rs, q.src = some s →
      ∃ e ∈ openedOf c ds, e.1 = s ∧ q.pos < 2 ^ e.2.2
  | [], _, q, hq, _ => by simp [readsOf] at hq
  | _ :: _, [], q, hq, _ => by simp [readsOf] at hq
  | d :: ds, R :: Rs, q, hq, hs => by
    simp only [readsOf, List.mem_append, List.mem_flatMap, List.mem_map] at hq
    rcases hq with (⟨t, _, x, _, rfl⟩ | ⟨o, ho, x, hx, rfl⟩) | hq
    · cases hs
    · refine ⟨(srcOf c o.2, d.entry.poss, o.1.a), ?_, Option.some.inj hs, ?_⟩
      · unfold openedOf
        rw [List.flatMap_cons]
        exact List.mem_append_left _ (List.mem_map.2 ⟨o, ho, rfl⟩)
      · obtain ⟨y, _, rfl⟩ := List.mem_map.1 (mem_listOf x _ hx)
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · obtain ⟨e, he, h1, h2⟩ := reads_pos ds Rs q hq hs
      refine ⟨e, ?_, h1, h2⟩
      unfold openedOf
      rw [List.flatMap_cons]
      exact List.mem_append_right _ he

end Chain

/-! ## 4 The three chains -/

theorem asks_len (F : FileDescription Xi) (ρ : Draws) (hρ : ρ.due F = true) (ch k : ℕ) :
    (treeAsks F ρ ch k).length ≤
      (((openedAll F.roundsDeclaredByBlocks).filter (·.1 == (ch, k))).map (·.2.1)).sum := by
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, _⟩ := hρ
  unfold treeAsks allBare bareReads openedAll
  rw [List.length_map, List.filter_append, List.filter_append, List.length_append,
    List.length_append, List.filter_append, List.filter_append, List.map_append, List.map_append,
    List.sum_append, List.sum_append]
  exact Nat.add_le_add (Nat.add_le_add (reads_len 0 0 _ _ (ch, k) _ _ h1)
    (reads_len 1 0 _ _ (ch, k) _ _ h2)) (reads_len 2 F.lastChainFirstTreeNumber _ _ (ch, k) _ _ h3)

theorem asks_pos (F : FileDescription Xi) (ρ : Draws) (ch k x : ℕ) (hx : x ∈ treeAsks F ρ ch k) :
    ∃ e ∈ openedAll F.roundsDeclaredByBlocks, e.1 = (ch, k) ∧ x < 2 ^ e.2.2 := by
  unfold treeAsks at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hq, hs⟩ := List.mem_filter.1 hq
  have hs' : q.src = some (ch, k) := beq_iff_eq.1 hs
  unfold allBare bareReads at hq
  unfold openedAll
  rcases List.mem_append.1 hq with hq | hq
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨e, he, h1, h2⟩ := reads_pos 0 0 _ _ (ch, k) _ _ q hq hs'
      exact ⟨e, List.mem_append_left _ (List.mem_append_left _ he), h1, h2⟩
    · obtain ⟨e, he, h1, h2⟩ := reads_pos 1 0 _ _ (ch, k) _ _ q hq hs'
      exact ⟨e, List.mem_append_left _ (List.mem_append_right _ he), h1, h2⟩
  · obtain ⟨e, he, h1, h2⟩ := reads_pos 2 F.lastChainFirstTreeNumber _ _ (ch, k) _ _ q hq hs'
    exact ⟨e, List.mem_append_right _ he, h1, h2⟩

/-! ## 5 The library's test "once" -/

theorem srcs_chain (c : ℕ) (ds : List Fmt.DeclaredRound)
    (mk : Fmt.DeclaredRound → Fmt.Shape × Fmt.TreeSource → VerifiableInference.Desc.BookPlan.Opening)
    (hmk : ∀ d o, ((mk d o).chain, (mk d o).sent) = srcOf c o.2) :
    (openedOf c ds).map (·.1) =
      (ds.flatMap fun d => d.opens.map (mk d)).map fun o => (o.chain, o.sent) := by
  unfold openedOf
  rw [List.map_flatMap, List.map_flatMap]
  refine congrArg List.flatten (List.map_congr_left fun d _ => ?_)
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun o _ => (hmk d o).symm

/-- The sources in `openedAll` are those of the library's list of openings, in the same order. -/
theorem srcs_openings (D : BookPlan.DeclaredRoundsByChain) :
    (openedAll D).map (·.1) = (BookPlan.openings D).map fun o => (o.chain, o.sent) := by
  have z : [D.1, D.2.1, D.2.2].zipIdx = [(D.1, 0), (D.2.1, 1), (D.2.2, 2)] := rfl
  unfold openedAll BookPlan.openings
  rw [z]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
  rw [List.append_assoc]
  refine congrArg₂ _ (srcs_chain 0 D.1 _ fun d o => ?_)
    (congrArg₂ _ (srcs_chain 1 D.2.1 _ fun d o => ?_) (srcs_chain 2 D.2.2 _ fun d o => ?_)) <;>
  · obtain ⟨sh, src⟩ := o
    cases src <;> rfl

/-- **A tree that is told with a tenant that is not sampled has one opening at most.** -/
theorem opens_once (D : BookPlan.DeclaredRoundsByChain) (T : BookPlan.SentOraclesByChain) (h : BookPlan.once D T = true)
    (ch k : ℕ) (r : Oracle) (hr : (T[ch]?).bind (·[k]?) = some r)
    (hs : r.tenants.all (·.sampled) = false) :
    ((openedAll D).filter (·.1 == (ch, k))).length ≤ 1 := by
  have e1 : ((openedAll D).filter (·.1 == (ch, k))).length =
      ((BookPlan.openings D).filter fun p => p.chain == ch && p.sent == k).length := by
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    have a : (openedAll D).countP (·.1 == (ch, k)) =
        ((openedAll D).map (·.1)).countP (· == (ch, k)) := by
      rw [List.countP_map]
      rfl
    rw [a, srcs_openings, List.countP_map]
    refine List.countP_congr fun p _ => ?_
    show ((p.chain, p.sent) == (ch, k)) = true ↔ (p.chain == ch && p.sent == k) = true
    rw [beq_iff_eq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, Prod.mk.injEq]
  rw [e1]
  cases hl : (BookPlan.openings D).filter fun p => p.chain == ch && p.sent == k with
  | nil => exact Nat.zero_le _
  | cons p l =>
    rw [← hl]
    have hp : p ∈ (BookPlan.openings D).filter fun p => p.chain == ch && p.sent == k := by
      rw [hl]
      exact List.mem_cons_self
    obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp2
    have := List.all_eq_true.1 h p hp1
    unfold VerifiableInference.Desc.BookPlan.onSymbolComponents VerifiableInference.Desc.BookPlan.rootOf
      at this
    rw [hp2.1, hp2.2, hr] at this
    simpa [hs] using this

/-! ## 6 Together -/

/-- **Where such a tree has an opening that samples P positions and states the depth a.** -/
theorem asks_of_one (F : FileDescription Xi) (hb : F.treeSharingOk = true) (ρ : Draws) (hρ : ρ.due F = true)
    (ch k P a : ℕ) (r : Oracle) (hr : (F.roots[ch]?).bind (·[k]?) = some r)
    (hs : r.tenants.all (·.sampled) = false) (he : ((ch, k), P, a) ∈ openedAll F.roundsDeclaredByBlocks) :
    (treeAsks F ρ ch k).length ≤ P ∧ ∀ x ∈ treeAsks F ρ ch k, x < 2 ^ a := by
  have ho : BookPlan.once F.roundsDeclaredByBlocks F.roots = true :=
    VerifiableInference.Desc.BookPlan.ok_clause
      (show VerifiableInference.Desc.BookPlan.allClausesHold F.roundsDeclaredByBlocks F.roots = true from hb)
      (x := ("once", BookPlan.once F.roundsDeclaredByBlocks F.roots))
      (by simp [VerifiableInference.Desc.BookPlan.clauses])
  have h1 := opens_once F.roundsDeclaredByBlocks F.roots ho ch k r hr hs
  have hm : ((ch, k), P, a) ∈ (openedAll F.roundsDeclaredByBlocks).filter (·.1 == (ch, k)) :=
    List.mem_filter.2 ⟨he, beq_self_eq_true _⟩
  have hl : (openedAll F.roundsDeclaredByBlocks).filter (·.1 == (ch, k)) = [((ch, k), P, a)] := by
    cases hf : (openedAll F.roundsDeclaredByBlocks).filter (·.1 == (ch, k)) with
    | nil => rw [hf] at hm; cases hm
    | cons y l =>
      rw [hf] at hm h1
      cases l with
      | nil => rw [List.mem_singleton.1 hm]
      | cons _ _ => simp at h1
  refine ⟨?_, fun x hx => ?_⟩
  · have := asks_len F ρ hρ ch k
    rw [hl] at this
    simpa using this
  · obtain ⟨e, he', h2, h3⟩ := asks_pos F ρ ch k x hx
    have : e ∈ (openedAll F.roundsDeclaredByBlocks).filter (·.1 == (ch, k)) :=
      List.mem_filter.2 ⟨he', by rw [h2]; exact beq_self_eq_true _⟩
    rw [hl] at this
    rw [List.mem_singleton.1 this] at h3
    exact h3

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.openedOf
#print axioms ProofFile.Honest.K12.Light.openedAll
#print axioms ProofFile.Honest.K12.Light.length_insertN
#print axioms ProofFile.Honest.K12.Light.mem_insertN
#print axioms ProofFile.Honest.K12.Light.length_listOf
#print axioms ProofFile.Honest.K12.Light.mem_listOf
#print axioms ProofFile.Honest.K12.Light.opens_len
#print axioms ProofFile.Honest.K12.Light.reads_len
#print axioms ProofFile.Honest.K12.Light.reads_pos
#print axioms ProofFile.Honest.K12.Light.asks_len
#print axioms ProofFile.Honest.K12.Light.asks_pos
#print axioms ProofFile.Honest.K12.Light.srcs_chain
#print axioms ProofFile.Honest.K12.Light.srcs_openings
#print axioms ProofFile.Honest.K12.Light.opens_once
#print axioms ProofFile.Honest.K12.Light.asks_of_one
