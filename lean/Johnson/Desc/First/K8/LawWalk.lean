-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawWalk.lean: THE SMALLNESS TEST: THE TEST `Named.namedAt` AT THE RECORD IN
FRONT OF THE DRAW, FROM WHAT A WALK OVER THE LINK'S BLOCKS HANDS ON: ONE JOINING, IN THE FORMS IN
WHICH THE OTHER LAWS END.

  `WalkGives a b b' s`: what a walk from the link's first sending to the record s in front of the
    draw hands on, with a, b, b' the record's counts of roots in front of the first sending, behind
    it, and in front of the draw: the book's two invariants (`Book.BookFits`, `Named.BookHas`); and
    of the open link's record L: the public test on the frame's shape; the frame's number of the
    link is the link's; the link has had at most two moments; every kept copy sits in a tree from a
    up to b; the frame's own messages sit, below the number of the link's messages of moment 0, in
    trees from a up to b, and from there on in trees from b up to b'.
  `PlanGives p a b'`: what ties these counts to the plan: the place names (for the matrices or for
    the reads: `p.matsIn ++ p.readsIn`: the test `Named.namedB` asks no more) every tree with a
    number from a up to b'.
  `namedAt_of_walk`: **with the guard of order at s (`Named.ordered`), these two give
    `Named.namedAt p s` = yes.**
  `planGives_of_ranges`: `PlanGives` from two ranges of the plan (the trees that the rounds of
    entries iM and iR send) and four equations on the record's counts of roots. `ranges_of_namesB`:
    the two ranges from the test `namesB` (Johnson/Desc/First/K8/PlanNames.lean).
Definitions, statement and proof: by calls of LawBookNames.lean, LawOrdered.lean, LawPlanNames.lean.
Limits. NEITHER STRUCTURE IS SHOWN OF ANY RECORD OR PLAN HERE: the first is another file's walk's
to give, the second's counts a law on every block in front ("a yes adds to the count of roots what
the block's declared rounds send") and a test that has run nowhere yet. Nothing on soundness.

-/
import Johnson.Desc.First.K8.LawOrdered
import Johnson.Desc.First.K8.LawPlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Named
open OnBytes OnBytes.Model

/-- What a walk over the link's blocks hands on at the record in front of the draw. -/
structure WalkGives (a b b' : Nat) (s : S) : Prop where
  fits : Book.BookFits s.book
  has : BookHas s
  shape : ∀ L, s.link? = some L → reqShapeOk L.check.frame.shape = true
  link : ∀ L, s.link? = some L → L.check.frame.link = L.link
  moments : ∀ L, s.link? = some L → L.moments ≤ 2
  kept : ∀ L, s.link? = some L → ∀ o ∈ L.check.frame.keptBefore.toList,
    ∃ jt : Nat × Nat, s.book.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b
  own : ∀ L, s.link? = some L → ∀ j o : Nat, L.check.frame.own[j]? = some o →
    ∃ jt : Nat × Nat, s.book.place[o]? = some jt ∧
      ((j < (L.check.frame.atMoment 0).length ∧ a ≤ jt.1 ∧ jt.1 < b) ∨
        ((L.check.frame.atMoment 0).length ≤ j ∧ b ≤ jt.1 ∧ jt.1 < b'))

/-- What ties the three counts to the plan: the place names every tree with a number from a up to
b'. -/
def PlanGives (p : Par) (a b' : Nat) : Prop :=
  ∀ j, a ≤ j → j < b' → j ∈ p.matsIn ++ p.readsIn

/-- **The joining.** -/
theorem namedAt_of_walk {p : Par} {s : S} {a b b' : Nat} (hO : ordered s = some true)
    (W : WalkGives a b b' s) (hab : a ≤ b) (hbb : b ≤ b') (P : PlanGives p a b') :
    namedAt p s = true := by
  obtain ⟨tl, L, ht, hl, ho⟩ := ordered_spec hO
  exact namedAt_of_inv (a := a) (b := b) (a' := b) (b' := b') ht hl W.fits W.has
    (sentHere_of_cut_shape (W.shape L hl) (W.kept L hl) (W.own L hl))
    (earlyB_of_order ho (W.link L hl) (W.moments L hl)) ho
    (fun j h1 h2 => P j h1 (Nat.lt_of_lt_of_le h2 hbb)) fun j h1 h2 => P j (Nat.le_trans hab h1) h2

/-- `PlanGives` from two ranges of the plan: where a is the number of trees that the rounds of the
entries in front of entry iM send, b that number behind entry iM and also the number in front of
entry iR, and b' the number behind entry iR. -/
theorem planGives_of_ranges {Xi : Type} {F : FileDescription Xi} {p : Par} {iM iR a b b' : Nat}
    {bM bR : Block F.S₁ F.Cl}
    (hn : ∀ j, (treesFrom F iM ≤ j ∧ j < treesFrom F iM + rootsOfRounds bM.rounds) ∨
      (treesFrom F iR ≤ j ∧ j < treesFrom F iR + rootsOfRounds bR.rounds) →
      j ∈ p.matsIn ++ p.readsIn)
    (front : a = treesFrom F iM) (behind : b = a + rootsOfRounds bM.rounds)
    (reads : b = treesFrom F iR) (draw : b' = b + rootsOfRounds bR.rounds) :
    PlanGives p a b' := by
  intro j h1 h2
  by_cases hj : j < b
  · exact hn j (Or.inl ⟨front ▸ h1, by rw [← front, ← behind]; exact hj⟩)
  · exact hn j (Or.inr ⟨reads ▸ Nat.le_of_not_lt hj, by rw [← reads, ← draw]; exact h2⟩)

/-- The two ranges from the test `namesB`. -/
theorem ranges_of_namesB {Xi : Type} {F : FileDescription Xi} {p : Par} {iM iR : Nat}
    (h : namesB F p iM iR = true) :
    ∃ bM bR, F.first.blocksInOrder[iM]? = some bM ∧ F.first.blocksInOrder[iR]? = some bR ∧
      ∀ j, (treesFrom F iM ≤ j ∧ j < treesFrom F iM + rootsOfRounds bM.rounds) ∨
        (treesFrom F iR ≤ j ∧ j < treesFrom F iR + rootsOfRounds bR.rounds) →
        j ∈ p.matsIn ++ p.readsIn := by
  obtain ⟨bM, bR, eM, eR, hM, hR⟩ := names_of_test h
  refine ⟨bM, bR, eM, eR, fun j hj => ?_⟩
  rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact List.mem_append_left _ (hM j h1 h2)
  · exact List.mem_append_right _ (hR j h1 h2)

end VerifiableInference.Desc.First.K8.Named

#print axioms VerifiableInference.Desc.First.K8.Named.namedAt_of_walk
#print axioms VerifiableInference.Desc.First.K8.Named.planGives_of_ranges
#print axioms VerifiableInference.Desc.First.K8.Named.ranges_of_namesB
