-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/TrueLaid.lean: the `front` that rounds as produced give is
true to these rounds: the closed form of what a part is shown (`laidOf`, Honest/Law/Rule/Words.lean;
`Laid.front`, Honest/Law/Rule/Session.lean) meets `TrueTo` (Honest/Thread/OnFrom.lean) at the tables
of these very rounds (`envOf`, Honest/Law/Cut.lean), chain by chain, at any rounds as produced and
any list of challenges. The bound on the positions is two to the greatest depth at which a declared
round opens the tree: a function of the description alone.

  1  `opensIn`, `depthAt`   the depth at which a tree is opened
  2  `le_foldl_max`, `reads_below`, `treeAsks_below`   the positions read of a tree lie below two to
     that depth
  3  `join_some`, `tree_true`, `stored_true`   a tree; the stored columns
  4  `trueTo_one`, `trueTo_two`, `trueTo_three`   chain by chain

Limits.
  * That a table as produced has just that depth is not said here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Fmt.Rules6Laws
import Johnson.Desc.ProofFile.Honest.Law.RunsFile
import Johnson.Desc.ProofFile.Honest.Thread.OnFrom
import Johnson.Desc.ProofFile.Honest.Law.Rule.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)

variable {Xi : Type}

/-! ## 1 The depth at which a tree is opened -/

/-- The depths at which rounds of chain number ch open tree number j of chain number c. -/
def opensIn (ch : Nat) (ds : List Fmt.DeclaredRound) (c j : Nat) : List Nat :=
  (ds.flatMap (·.opens)).filterMap fun o => if srcOf ch o.2 = (c, j) then some o.1.a else none

/-- The greatest of them, over the three chains' declared rounds; 0 where no round opens the
tree. -/
def depthAt (F : FileDescription Xi) (c j : Nat) : Nat :=
  (opensIn 0 F.roundsDeclaredByBlocks.1 c j ++ opensIn 1 F.roundsDeclaredByBlocks.2.1 c j ++ opensIn 2 F.roundsDeclaredByBlocks.2.2 c j).foldl max 0

/-! ## 2 The positions read of a tree lie below two to that depth -/

theorem le_foldl_max : ∀ (l : List Nat) (b a : Nat), (a ≤ b ∨ a ∈ l) → a ≤ l.foldl max b
  | [], _, _, h => h.elim id fun h' => by cases h'
  | x :: l, b, a, h => by
    refine le_foldl_max l (max b x) a ?_
    rcases h with h | h
    · exact Or.inl (Nat.le_trans h (Nat.le_max_left _ _))
    · rcases List.mem_cons.1 h with e | e
      · exact Or.inl (by rw [e]; exact Nat.le_max_right _ _)
      · exact Or.inr e

theorem reads_below (ch ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (c j : Nat) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), ∀ q ∈ readsOf ch ft stored tree ds Rs,
    q.src = some (c, j) → ∃ a ∈ opensIn ch ds c j, q.pos < 2 ^ a
  | [], _, q, hq, _ => by
    simp only [readsOf] at hq
    cases hq
  | _ :: _, [], q, hq, _ => by
    simp only [readsOf] at hq
    cases hq
  | d :: ds, R :: Rs, q, hq, hs => by
    simp only [readsOf] at hq
    rcases List.mem_append.1 hq with hq | hq
    · rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨s, -, hq⟩ := List.mem_flatMap.1 hq
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
        cases hs
      · obtain ⟨o, ho, hq⟩ := List.mem_flatMap.1 hq
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
        obtain ⟨z, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ x).1 hx)
        refine ⟨o.1.a, ?_, Nat.mod_lt _ (Nat.pow_pos (by decide))⟩
        unfold opensIn
        refine List.mem_filterMap.2 ⟨o, ?_, ?_⟩
        · rw [List.flatMap_cons]
          exact List.mem_append.2 (Or.inl ho)
        · rw [if_pos (Option.some.inj hs)]
    · obtain ⟨a, ha, hlt⟩ := reads_below ch ft stored tree c j ds Rs q hq hs
      refine ⟨a, ?_, hlt⟩
      unfold opensIn at ha ⊢
      obtain ⟨o, ho, e⟩ := List.mem_filterMap.1 ha
      refine List.mem_filterMap.2 ⟨o, ?_, e⟩
      rw [List.flatMap_cons]
      exact List.mem_append.2 (Or.inr ho)

/-- **Every position that is read of a tree lies below two to the depth at which it is opened.** -/
theorem treeAsks_below (F : FileDescription Xi) (ρ : Draws) (c j : Nat) :
    ∀ x ∈ treeAsks F ρ c j, x < 2 ^ depthAt F c j := by
  intro x hx
  unfold treeAsks at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hq1, hq2⟩ := List.mem_filter.1 hq
  have hs : q.src = some (c, j) := beq_iff_eq.1 hq2
  have key : ∃ a ∈ opensIn 0 F.roundsDeclaredByBlocks.1 c j ++ opensIn 1 F.roundsDeclaredByBlocks.2.1 c j ++ opensIn 2 F.roundsDeclaredByBlocks.2.2 c j,
      q.pos < 2 ^ a := by
    unfold allBare bareReads at hq1
    rcases List.mem_append.1 hq1 with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨a, ha, hl⟩ := reads_below 0 0 _ _ c j _ _ q h hs
        exact ⟨a, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl ha))), hl⟩
      · obtain ⟨a, ha, hl⟩ := reads_below 1 0 _ _ c j _ _ q h hs
        exact ⟨a, List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr ha))), hl⟩
    · obtain ⟨a, ha, hl⟩ := reads_below 2 F.lastChainFirstTreeNumber _ _ c j _ _ q h hs
      exact ⟨a, List.mem_append.2 (Or.inr ha), hl⟩
  obtain ⟨a, ha, hl⟩ := key
  exact Nat.lt_of_lt_of_le hl (Nat.pow_le_pow_right (by decide) (le_foldl_max _ 0 a (Or.inr ha)))

/-! ## 3 A tree; the stored columns -/

theorem join_some {α : Type} {o : Option (Option α)} {a : α} (h : o.join = some a) :
    o = some (some a) := by
  cases o with
  | none => cases h
  | some x =>
    cases x with
    | none => cases h
    | some y =>
      have : y = a := Option.some.inj h
      rw [this]

/-- **A tree of rounds as produced before: `front` lists it, at positions below two to the depth at
which it is opened, and each listed column is the table's own.** -/
theorem tree_true (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (Nat × Nat × List UInt64)) (ch c j : Nat) (hc : c ≤ 2) (hv : c = ch ∨ ch = 2)
    (pt : Place × Table) (h : ((tablesOf (pick3 l₀ l₁ l₂ c))[j]?).bind id = some pt) :
    ∃ cols, ((laidOf F ρ l₀ l₁ l₂).front ch st).treeCols c j = some cols ∧
      ∀ q ∈ cols, q.1 < 2 ^ depthAt F c j ∧ q.2 = pt.2.col q.1 := by
  have ht := tables_tabs (pick3 l₀ l₁ l₂ c) j
  rw [h] at ht
  have ht' := join_some ht.symm
  refine ⟨(treeAsks F ρ c j).map fun x => (x, pt.2.col x), ?_, ?_⟩
  · rw [treeCols_front F ρ l₀ l₁ l₂ st ch c j hc hv, ht']
    rfl
  · intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
    exact ⟨treeAsks_below F ρ c j x hx, rfl⟩

theorem stored_true (stored : Nat → Nat → Option (List UInt64)) (asked : List (Nat × Nat)) :
    ∀ q ∈ storedShown stored asked, stored q.1 q.2.1 = some q.2.2 := by
  intro q hq
  unfold storedShown at hq
  obtain ⟨a, -, e⟩ := List.mem_filterMap.1 hq
  cases hs : stored a.1 a.2 with
  | none =>
    rw [hs] at e
    cases e
  | some w =>
    rw [hs] at e
    have e' : (a.1, a.2, w) = q := Option.some.inj e
    rw [← e']
    exact hs

/-! ## 4 Chain by chain -/

theorem trueTo_one (F : FileDescription Xi) (stored : Nat → Nat → Option (List UInt64)) (ρ : Draws)
    (p : List Played) :
    TrueTo 0 (depthAt F) ((laidOf F ρ p [] []).front 0 (storedShown stored (storedAsks F ρ)))
      (roundsOf p) (envOf stored (fun _ _ => none) p) := by
  refine ⟨roundsOff_by 0 (treeAsks F ρ 0) p 0, ?_, stored_true stored _⟩
  intro c j pt h
  by_cases hc : c = 0
  · subst hc
    exact tree_true F ρ p [] [] _ 0 0 j (by decide) (Or.inl rfl) pt h
  · have e : treeSrc 0 c j = .taken c j := by
      unfold treeSrc
      rw [if_neg (by simpa using hc)]
    rw [e] at h
    cases h

theorem trueTo_two (F : FileDescription Xi) (stored : Nat → Nat → Option (List UInt64)) (ρ : Draws)
    (p : List Played) :
    TrueTo 1 (depthAt F) ((laidOf F ρ [] p []).front 1 (storedShown stored (storedAsks F ρ)))
      (roundsOf p) (envOf stored (fun _ _ => none) p) := by
  refine ⟨roundsOff_by 1 (treeAsks F ρ 1) p 0, ?_, stored_true stored _⟩
  intro c j pt h
  by_cases hc : c = 1
  · subst hc
    exact tree_true F ρ [] p [] _ 1 1 j (by decide) (Or.inl rfl) pt h
  · have e : treeSrc 1 c j = .taken c j := by
      unfold treeSrc
      rw [if_neg (by simpa using hc)]
    rw [e] at h
    cases h

theorem trueTo_three (F : FileDescription Xi) (stored : Nat → Nat → Option (List UInt64)) (ρ : Draws)
    (p₀ p₁ p : List Played) :
    TrueTo 2 (depthAt F) ((laidOf F ρ p₀ p₁ p).front 2 (storedShown stored (storedAsks F ρ)))
      (roundsOf p₀ ++ roundsOf p₁ ++ roundsOf p) (envOf stored (taken₃ p₀ p₁) p) := by
  refine ⟨?_, ?_, stored_true stored _⟩
  · show roundsOff (shownBy 0 (treeAsks F ρ 0) p₀ 0 ++ shownBy 1 (treeAsks F ρ 1) p₁ 0 ++
      shownBy 2 (treeAsks F ρ 2) p 0) = _
    unfold roundsOff
    rw [List.map_append, List.map_append]
    exact congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (roundsOff_by 0 _ p₀ 0) (roundsOff_by 1 _ p₁ 0))
      (roundsOff_by 2 _ p 0)
  · intro c j pt h
    by_cases h2 : c = 2
    · subst h2
      exact tree_true F ρ p₀ p₁ p _ 2 2 j (by decide) (Or.inl rfl) pt h
    · have e : treeSrc 2 c j = .taken c j := by
        unfold treeSrc
        rw [if_neg (by simpa using h2)]
      rw [e] at h
      have h' : taken₃ p₀ p₁ c j = some pt := h
      unfold taken₃ at h'
      by_cases h0 : c = 0
      · subst h0
        exact tree_true F ρ p₀ p₁ p _ 2 0 j (by decide) (Or.inr rfl) pt h'
      · rw [if_neg (by simpa using h0)] at h'
        by_cases h1 : c = 1
        · subst h1
          exact tree_true F ρ p₀ p₁ p _ 2 1 j (by decide) (Or.inr rfl) pt h'
        · rw [if_neg (by simpa using h1)] at h'
          cases h'

end ProofFile.Honest

#print axioms ProofFile.Honest.le_foldl_max
#print axioms ProofFile.Honest.reads_below
#print axioms ProofFile.Honest.treeAsks_below
#print axioms ProofFile.Honest.join_some
#print axioms ProofFile.Honest.tree_true
#print axioms ProofFile.Honest.stored_true
#print axioms ProofFile.Honest.trueTo_one
#print axioms ProofFile.Honest.trueTo_two
#print axioms ProofFile.Honest.trueTo_three
