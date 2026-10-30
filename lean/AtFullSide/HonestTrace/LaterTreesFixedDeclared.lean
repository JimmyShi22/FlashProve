-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/HonestTrace/LaterTreesFixedDeclared.lean

Nothing on hiding. No property of the protocol is claimed. Public counts alone.

AT A DESCRIPTION THAT PASSES ITS OWN TEST ON THE PLAN: EACH SOURCE DECLARED AS TAKEN OVER THAT A ROUND OF THE LAST CHAIN OPENS NAMES CHAIN 0 OR 1 AND A
TREE THAT THIS CHAIN DECLARES: the premise "TakenAreDeclared" (LaterTreesFixed.lean) at the value "takenSourcesOpened" of the letter "taken".

* "roots_counted_are_trees_declared": over a list of sub-protocols each of which declares one oracle message for each root, the roots that the rounds
  count are the trees declared. (The like stands in Honest/Thread/OpensOfPlan.lean, "roots_eq_trees".)
* "tree_declared_of_sending_round": a root that has a sending round is a tree that the chain declares.
* "shaped_roots": a sub-protocol that passes "Block.shaped" declares one oracle message for each root.
* "taken_opened_are_declared": THE END, from "planOk".

By what. The clause "inTime" of the plan's test on the book (Johnson/Desc/BookPlan.lean), its arm at a taken source; "inTime_plan", "root_lt",
"sum_take_le", "mem_zipIdx_of" (Honest/Law/PlanGives.lean); "planOk_all" (Honest/Thread/File.lean); "shaped_parts" (Honest/Law/Data.lean).

Limits. General in the description. Counts only.
-/
import AtFullSide.HonestTrace.LaterTreesFixed
import Johnson.Desc.ProofFile.Honest.Law.PlanGives
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun.LaterTrees
open VerifiableInference.Desc
open ProofFile.Honest ProofFile.Honest.FirstThread

variable {S Cl Xi : Type}

/-- **The roots that the rounds count are the trees declared.** -/
theorem roots_counted_are_trees_declared : ∀ bs : List (Block S Cl),
    (∀ x ∈ bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) →
    ((bs.flatMap (·.rounds)).map (·.entry.roots)).sum =
      (bs.flatMap fun x => x.oracles.flatMap id).length
  | [], _ => rfl
  | x :: l, h => by
    have e : (x.oracles.flatMap id).length = (x.oracles.map (·.length)).sum := by
      rw [List.length_flatMap]
      rfl
    rw [List.flatMap_cons, List.flatMap_cons, List.map_append, List.sum_append, List.length_append,
      h x List.mem_cons_self, e,
      roots_counted_are_trees_declared l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **A root that has a sending round is a tree that the chain declares.** -/
theorem tree_declared_of_sending_round {bs : List (Block S Cl)}
    (hor : ∀ x ∈ bs, x.rounds.map (·.entry.roots) = x.oracles.map (·.length)) {j : Nat}
    (h : (BookPlan.roundOfRoot (bs.flatMap (·.rounds)) j).isSome = true) :
    j < treesTo bs bs.length := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
  have h1 := root_lt _ j i hi
  rw [List.map_take] at h1
  have h2 := sum_take_le ((bs.flatMap (·.rounds)).map (·.entry.roots)) (i + 1)
    (i + 1 + ((bs.flatMap (·.rounds)).map (·.entry.roots)).length) (Nat.le_add_right _ _)
  rw [List.take_of_length_le (Nat.le_add_left _ _), roots_counted_are_trees_declared bs hor] at h2
  unfold treesTo
  rw [List.take_length]
  omega

/-- Two lists of equal length whose members agree pair by pair have equal images. -/
theorem images_agree {α β : Type} (f : α → Nat) (g : β → Nat) : ∀ (l : List α) (m : List β),
    m.length = l.length → (∀ z ∈ l.zip m, g z.2 = f z.1) → l.map f = m.map g
  | [], [], _, _ => rfl
  | a :: l, b :: m, hl, h => by
    rw [List.map_cons, List.map_cons, h (a, b) (by simp),
      images_agree f g l m (by simpa using hl) fun z hz => h z (by
        rw [List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hz)]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **A sub-protocol that passes "Block.shaped" declares one oracle message for each root.** -/
theorem shaped_roots {b : Block S Cl} (h : b.shaped = true) :
    b.rounds.map (·.entry.roots) = b.oracles.map (·.length) := by
  obtain ⟨h1, h2⟩ := shaped_parts h
  exact images_agree _ _ _ _ h1 h2

/-- **THE END: at a description that passes its test on the plan.** -/
theorem taken_opened_are_declared {F : FileDescription Xi} (hp : F.planOk = true) :
    TakenAreDeclared (takenSourcesOpened F.second.blocksInOrder) F.first.blocksInOrder F.shared.blocksInOrder := by
  obtain ⟨s1, s2, -⟩ := planOk_all hp
  intro σ hσ
  obtain ⟨hm, ht⟩ := List.mem_filter.1 hσ
  obtain ⟨d, hd, ho⟩ := List.mem_flatMap.1 hm
  obtain ⟨o, ho', rfl⟩ := List.mem_map.1 ho
  have hT := inTime_plan hp
  unfold BookPlan.inTime at hT
  have h1 := List.all_eq_true.1 hT (F.roundsDeclaredByBlocks.2.2, 2) (.tail _ (.tail _ (.head _)))
  obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 hd
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 h1 (d, r) (by
    have e := mem_zipIdx_of _ 0 r d hr
    rw [Nat.zero_add] at e
    exact e)) o ho'
  cases hs : o.2 with
  | own t =>
    rw [hs] at ht
    cases ht
  | taken c j =>
    rw [hs] at h3
    have h3' : ((2 : Nat) == 2 && decide (c < 2) &&
        (BookPlan.roundOfRoot (([F.roundsDeclaredByBlocks.1, F.roundsDeclaredByBlocks.2.1, F.roundsDeclaredByBlocks.2.2][c]?).getD []) j).isSome) =
        true := h3
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h3'
    obtain ⟨⟨-, hc⟩, hsome⟩ := h3'
    match c, hc, hsome with
    | 0, _, hsome =>
      exact Or.inl ⟨j, rfl, tree_declared_of_sending_round
        (fun x hx => shaped_roots (s1 x hx).2) hsome⟩
    | 1, _, hsome =>
      exact Or.inr ⟨j, rfl, tree_declared_of_sending_round
        (fun x hx => shaped_roots (s2 x hx).2) hsome⟩

end HonestTraceRun.LaterTrees

#print axioms HonestTraceRun.LaterTrees.roots_counted_are_trees_declared
#print axioms HonestTraceRun.LaterTrees.tree_declared_of_sending_round
#print axioms HonestTraceRun.LaterTrees.shaped_roots
#print axioms HonestTraceRun.LaterTrees.taken_opened_are_declared
