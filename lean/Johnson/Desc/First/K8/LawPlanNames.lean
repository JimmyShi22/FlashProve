-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPlanNames.lean: THE SMALLNESS TEST: WHAT THE PUBLIC TEST `namesB` GIVES;
AND THAT THE BLOCK OF THE DRAW SENDS NO TREE, BY ITS DECLARED ROUND AND BY ITS YES.

  `rootsOfRounds_eq`, `roundsOfBlocks_eq`: the two counts of Johnson/Desc/First/K8/PlanNames.lean
    are `rootsIn` (LawSeats.lean) and `roundsIn` (LawBefore.lean).
  `names_of_test`: **a yes of `namesB F p iM iR`**: there are the two entries bM and bR, and every
    number from `treesFrom F iM` up to that plus the trees of bM's rounds is among `p.matsIn`; the
    like for bR and `p.readsIn`: the two facts on the plan that
    Johnson/Desc/First/K8/LawOrdered.lean's `namedAt_of_lists` asks, at a := `treesFrom F iM`,
    b := a + the trees of bM's rounds, a' := `treesFrom F iR`, b' := a' + the trees of bR's rounds.
  `draws_of_test`: a yes of `drawsB F ixs`: every declared round of the first chain that draws
    entries of a matrix stands right behind the rounds of the entries in front of one of the entries
    ixs.
  `round_roots`, `hear_rounds_roots`: the round of the draw declares no tree.
  `hear_roots_step`: **a yes of the block of the draw adds to the record's count of roots just what
    its declared rounds send: nothing.**
Statements and proofs.
Limits. `drawsB` READS THE FIRST CHAIN'S DECLARED ROUNDS ALONE: that the file's two other chains
draw no such entries is `noDrawElseB` (PlanNames.lean); the key file's and the entry file's
descriptions are other files'. `namesB` is shown true at no description here. THAT THE RECORD'S
COUNT OF ROOTS IN FRONT OF ENTRY i IS `treesFrom F i` is another law, on all blocks in front.

-/
import Johnson.Desc.First.K8.PlanNames
import Johnson.Desc.First.K8.LawSeats
import Johnson.Desc.First.K8.LawLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

theorem rootsOfRounds_eq (ds : List Fmt.DeclaredRound) : rootsOfRounds ds = rootsIn ds := rfl

theorem roundsOfBlocks_eq {S Cl : Type} (l : List (Block S Cl)) : roundsOfBlocks l = roundsIn l :=
  rfl

/-- **What a yes of the test gives.** -/
theorem names_of_test {Xi : Type} {F : FileDescription Xi} {p : Par} {iM iR : Nat}
    (h : namesB F p iM iR = true) :
    ∃ bM bR, F.first.blocksInOrder[iM]? = some bM ∧ F.first.blocksInOrder[iR]? = some bR ∧
      (∀ j, treesFrom F iM ≤ j → j < treesFrom F iM + rootsOfRounds bM.rounds → j ∈ p.matsIn) ∧
      ∀ j, treesFrom F iR ≤ j → j < treesFrom F iR + rootsOfRounds bR.rounds → j ∈ p.readsIn := by
  unfold namesB at h
  cases hM : F.first.blocksInOrder[iM]? with
  | none => simp [hM] at h
  | some bM =>
    cases hR : F.first.blocksInOrder[iR]? with
    | none => simp [hM, hR] at h
    | some bR =>
      simp only [hM, hR, Bool.and_eq_true, beq_iff_eq] at h
      refine ⟨bM, bR, rfl, rfl, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
      · rw [h.1]
        exact List.mem_range'_1.2 ⟨h1, h2⟩
      · rw [h.2]
        exact List.mem_range'_1.2 ⟨h1, h2⟩

/-- **What a yes of `drawsB` gives**: a declared round of the first chain that draws entries of a
matrix is the round right behind the rounds of the entries in front of one of the listed entries. -/
theorem draws_of_test {Xi : Type} {F : FileDescription Xi} {ixs : List Nat} (h : drawsB F ixs = true)
    {j : Nat} {d : Fmt.DeclaredRound} (hj : F.roundsDeclaredByBlocks.1[j]? = some d) (ht : d.entry.trits ≠ 0) :
    ∃ i ∈ ixs, j = roundsIn (F.first.blocksInOrder.take i) := by
  unfold drawsB at h
  have e := beq_iff_eq.1 h
  have hm : j ∈ (List.range F.roundsDeclaredByBlocks.1.length).filter fun j =>
      ((F.roundsDeclaredByBlocks.1[j]?).map fun d => d.entry.trits != 0).getD false := by
    refine List.mem_filter.2 ⟨List.mem_range.2 (List.getElem?_eq_some_iff.1 hj).1, ?_⟩
    simp [hj, ht]
  rw [e] at hm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hm
  exact ⟨i, hi, rfl⟩

/-- The round of the draw declares no tree. -/
theorem round_roots (p : Par) : (round p).entry.roots = 0 := rfl

theorem hear_rounds_roots {S Cl : Type} (seat : Seat S) (p : Par) :
    rootsOfRounds (approximateRangeProofDrawKind (Cl := Cl) seat p).rounds = 0 := rfl

/-- **A yes of the block of the draw adds to the count of roots what its declared rounds send.** -/
theorem hear_roots_step {Cl : Type} (p : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (approximateRangeProofDrawKind (Cl := Cl) atS p).decide s rs gs = .ok s') :
    s'.roots = s.roots + rootsOfRounds (approximateRangeProofDrawKind (Cl := Cl) atS p).rounds := by
  rw [hear_rounds_roots]
  exact congrArg Prod.snd (hear_leaves_book_roots p s rs gs s' h)

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.names_of_test
#print axioms VerifiableInference.Desc.First.K8.draws_of_test
#print axioms VerifiableInference.Desc.First.K8.round_roots
#print axioms VerifiableInference.Desc.First.K8.hear_roots_step
