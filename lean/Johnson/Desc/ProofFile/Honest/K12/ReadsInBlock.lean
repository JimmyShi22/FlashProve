-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ReadsInBlock.lean: what declared rounds read
(`readsOf`, Johnson/Desc/ProofFile/Honest/Frame.lean), held at a stretch of a chain's rounds: each
round reads by its own challenge alone. So the reads of a stretch, at the same stretch of the
challenges, are among the whole list's; and where no round of a file outside one sub-protocol of the
shared chain opens a tree, all that is read of that tree in the whole file is read by that
sub-protocol's own rounds. General in the description. Public data alone: no input, no random value,
no run. It imports Mathlib.

  `reads_right`, `reads_take`, `reads_drop`, `reads_mid`   the reads of a stretch are among the
                 whole list's; no premise on lengths
  `reads_off`    where no opening of the rounds names a source, no read has it
  `aloneB`       a test with code on a description: no round of the file outside the sub-protocol b
                 of the shared list opens the shared chain's tree number k
  `asks_in_block`   where that test says yes, every member of the frame's list `treeAsks`
                 (Johnson/Desc/ProofFile/Honest/Law/Rule/Bare.lean) of that tree is the position of
                 a read that b's own rounds make at b's own stretch of the challenges

By what. `readsOf_append` (Johnson/Desc/ProofFile/Honest/Law/Cut.lean), `drawsFit_length`
(Law/Along.lean), `reads_pos`, `openedOf` (ReadsOfTree.lean).

Limits. Positions alone: nothing on what a column holds. `aloneB` is a premise of `asks_in_block`:
it is shown of no description here. `treeAsks` is computed of the declared rounds and the
challenges: that a run asks for no position beyond that list is not said here. The shared chain
alone. One list of challenges. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.ReadsOfTree
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block Place)

/-! ## 1 A stretch's reads -/

section Chain
variable (c ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
  (tree : Fmt.TreeSource → Option (Place × Table))

/-- At no challenge nothing is read. -/
theorem reads_right (D : List Fmt.DeclaredRound) : readsOf c ft stored tree D [] = [] := by
  cases D <;> simp [readsOf]

theorem reads_take : ∀ (len : ℕ) (D : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    ∀ q ∈ readsOf c ft stored tree (D.take len) (Rs.take len), q ∈ readsOf c ft stored tree D Rs
  | 0, _, _, q, hq => by simp [readsOf] at hq
  | _ + 1, [], _, q, hq => by simp [readsOf] at hq
  | _ + 1, _ :: _, [], q, hq => by simp [readsOf] at hq
  | len + 1, d :: D, R :: Rs, q, hq => by
    rw [List.take_succ_cons, List.take_succ_cons, readsOf] at hq
    rw [readsOf]
    rcases List.mem_append.1 hq with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (reads_take len D Rs q h)

theorem reads_drop : ∀ (n : ℕ) (D : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    ∀ q ∈ readsOf c ft stored tree (D.drop n) (Rs.drop n), q ∈ readsOf c ft stored tree D Rs
  | 0, _, _, _, hq => hq
  | _ + 1, [], _, q, hq => by simp [readsOf] at hq
  | _ + 1, _ :: _, [], q, hq => by
    rw [List.drop_nil, reads_right] at hq
    cases hq
  | n + 1, d :: D, R :: Rs, q, hq => by
    rw [List.drop_succ_cons, List.drop_succ_cons] at hq
    rw [readsOf]
    exact List.mem_append_right _ (reads_drop n D Rs q hq)

/-- **The reads of a stretch of declared rounds, at the same stretch of the challenges, are among
the whole list's.** No premise on lengths. -/
theorem reads_mid (D : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (n len : ℕ) :
    ∀ q ∈ readsOf c ft stored tree ((D.drop n).take len) ((Rs.drop n).take len),
      q ∈ readsOf c ft stored tree D Rs :=
  fun q hq => reads_drop c ft stored tree n D Rs q (reads_take c ft stored tree len _ _ q hq)

/-- Where no opening of the rounds names the source s, no read has it. -/
theorem reads_off (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (s : ℕ × ℕ)
    (h : ∀ e ∈ openedOf c ds, e.1 ≠ s) : ∀ q ∈ readsOf c ft stored tree ds Rs, q.src ≠ some s :=
  fun q hq hs => by
    obtain ⟨e, he, h1, -⟩ := reads_pos c ft stored tree s ds Rs q hq hs
    exact h e he h1

end Chain

/-! ## 2 A tree that one sub-protocol alone opens -/

/-- A test with code: no round of the file outside the sub-protocol between pre and t of the shared
list opens the shared chain's tree number k. -/
def aloneB {Xi : Type} (F : FileDescription Xi) (pre t : List (Block F.S₂ F.Cl)) (k : ℕ) : Bool :=
  (openedOf 0 F.roundsDeclaredByBlocks.1 ++ openedOf 1 (pre.flatMap (·.rounds)) ++
    openedOf 1 (t.flatMap (·.rounds)) ++ openedOf 2 F.roundsDeclaredByBlocks.2.2).all (·.1 != (1, k))

/-- **Where that test says yes: all that is read of the tree, in any round of the three chains, is
read by the sub-protocol's own rounds at its own stretch of the challenges.** -/
theorem asks_in_block {Xi : Type} {F : FileDescription Xi} (pre t : List (Block F.S₂ F.Cl))
    (b : Block F.S₂ F.Cl) (hcut : F.shared.blocksInOrder = pre ++ b :: t) (ρ : Draws)
    (hρ : ρ.due F = true) (k : ℕ) (ha : aloneB F pre t k = true) :
    ∀ x ∈ treeAsks F ρ 1 k, x ∈ ((readsOf 1 0 (fun _ _ => none) (fun _ => none) b.rounds
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take b.rounds.length)).filter fun q =>
        q.src == some (1, k)).map (·.pos) := by
  intro x hx
  unfold treeAsks at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hq, hs⟩ := List.mem_filter.1 hq
  have hs' : q.src = some (1, k) := beq_iff_eq.1 hs
  have off : ∀ e ∈ openedOf 0 F.roundsDeclaredByBlocks.1 ++ openedOf 1 (pre.flatMap (·.rounds)) ++
      openedOf 1 (t.flatMap (·.rounds)) ++ openedOf 2 F.roundsDeclaredByBlocks.2.2, e.1 ≠ (1, k) := fun e he =>
    bne_iff_ne.1 (List.all_eq_true.1 ha e he)
  unfold Draws.due at hρ
  simp only [Bool.and_eq_true] at hρ
  have h2 : drawsFit (F.shared.blocksInOrder.flatMap (·.rounds)) ρ.shared = true := hρ.1.1.2
  have hlen := ProofFile.Honest.drawsFit_length _ _ h2
  rw [hcut, List.flatMap_append, List.flatMap_cons, List.length_append, List.length_append]
    at hlen
  unfold allBare bareReads at hq
  rcases List.mem_append.1 hq with hq | hq
  · rcases List.mem_append.1 hq with hq | hq
    · exact absurd hs' (reads_off 0 0 _ _ _ _ (1, k) (fun e he => off e
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ he)))) q hq)
    · have hq' : q ∈ readsOf 1 0 (fun _ _ => none) (fun _ => none)
          (pre.flatMap (·.rounds) ++ (b.rounds ++ t.flatMap (·.rounds)))
          (ρ.shared.take (pre.flatMap (·.rounds)).length ++
            ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take b.rounds.length ++
              (ρ.shared.drop (pre.flatMap (·.rounds)).length).drop b.rounds.length)) := by
        rw [List.take_append_drop, List.take_append_drop, ← List.flatMap_cons,
          ← List.flatMap_append, ← hcut]
        exact hq
      rw [readsOf_append 1 0 _ _ _ _ _ _ (by rw [List.length_take]; omega),
        readsOf_append 1 0 _ _ _ _ _ _ (by rw [List.length_take, List.length_drop]; omega)] at hq'
      rcases List.mem_append.1 hq' with h | h
      · exact absurd hs' (reads_off 1 0 _ _ _ _ (1, k) (fun e he => off e
          (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ he)))) q h)
      · rcases List.mem_append.1 h with h | h
        · exact List.mem_map.2 ⟨q, List.mem_filter.2 ⟨h, hs⟩, rfl⟩
        · exact absurd hs' (reads_off 1 0 _ _ _ _ (1, k) (fun e he => off e
            (List.mem_append_left _ (List.mem_append_right _ he))) q h)
  · exact absurd hs' (reads_off 2 F.lastChainFirstTreeNumber _ _ _ _ (1, k) (fun e he => off e
                    (List.mem_append_right _ he)) q hq)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.reads_right
#print axioms ProofFile.Honest.K12.Light.reads_take
#print axioms ProofFile.Honest.K12.Light.reads_drop
#print axioms ProofFile.Honest.K12.Light.reads_mid
#print axioms ProofFile.Honest.K12.Light.reads_off
#print axioms ProofFile.Honest.K12.Light.aloneB
#print axioms ProofFile.Honest.K12.Light.asks_in_block
