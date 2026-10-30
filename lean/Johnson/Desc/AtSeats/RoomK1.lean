-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/RoomK1.lean: THE CONTENT OF THE FIELD k1 OF KeepShares
(Johnson/P1L20R/RoomKeep.lean), IN PLAIN LETTERS: every sub-protocol of the kind K1 that a lot of the
seat makes inside a link, but at the link's first place, hands on both clauses of the invariant beneath
room_at_reach, over any accepting step.

  k1_is_later      such a sub-protocol is one of the two of a segment's later places (Later,
                   Johnson/Desc/K1/Law/InOrderAtLater.lean), carried to the chain's type of claims: by
                   lot_K1 and k1_mem (Johnson/IMR/K1Seat.lean).
  k1_hands         StepYes 0 b' s s' → leftIsB n s = true → OutOf s.out.indexMasks s.st →
                   leftIsB n s' = true ∧ OutOf s'.out.indexMasks s'.st. NEITHER "chain 1" NOR "reached" NOR A
                   SCOPE IS SPENT. OutOf i T := ∀ G ∈ T.groups, i ∉ G.members: outOfGroupsB_iff's right side.

THE FIELD, OVER IT (typed here as a comment: no import line of this file names
Johnson/P1L20R/RoomKeep.lean; Johnson/P1L20R/RoomKeepK1.lean builds the field so):
  k1 := fun b' hm _ hk hl hp _ _ _ _ hy hout n hn =>
    (k1_hands b' hm hk hl hp hy hn (outOfGroupsB_iff.1 hout)).imp id outOfGroupsB_iff.2

What is not claimed. Nothing on soundness.
-/
import Johnson.IMR.K1Seat
import Johnson.Desc.K1.Law.GroupsAtLater
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes leftIsB)
open ProofFile (Cl)

/-- A sub-protocol of the kind K1 inside a link, not at its first place, is a later one. -/
theorem k1_is_later {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} (b' : Block S Cl)
    (hm : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) (hk : b'.place.kind = KindName.K1)
    (hl : b'.place.link ≠ none) (hp : b'.place.piece ≠ 1) :
    ∃ B own : Block S Unit, Later B own ∧ b' = B.retype := by
  obtain ⟨L, hL, hb⟩ := hm
  cases hq : b'.place.link with
  | none => exact absurd hq hl
  | some l =>
    obtain ⟨x, hx, rfl⟩ := IM.lot_K1 hL hb hk hq
    rcases IM.k1_mem hx with rfl | ⟨l', X, pr, pd, reads, digits, -, -, rfl | rfl⟩
    · exact absurd rfl hp
    · exact ⟨_, _, Later.reads Z G₀ l' X pr reads, rfl⟩
    · exact ⟨_, _, Later.digits G₀.first (gpOf Z) l' pd digits, rfl⟩

/-- **The field's content.** -/
theorem k1_hands {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} (b' : Block S Cl)
    (hm : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) (hk : b'.place.kind = KindName.K1)
    (hl : b'.place.link ≠ none) (hp : b'.place.piece ≠ 1) {s s' : S} (hy : StepYes 0 b' s s')
    {n : ℕ} (hn : leftIsB n s = true) (hO : OutOf s.out.indexMasks s.st) :
    leftIsB n s' = true ∧ OutOf s'.out.indexMasks s'.st := by
  obtain ⟨B, own, hB, rfl⟩ := k1_is_later b' hm hk hl hp
  obtain ⟨R, c, _, hs⟩ := hy
  obtain ⟨_, gs, hd⟩ := step_ok 0 _ s s' R c _ hs
  exact later_hands hB (rs := R.map noDigest) (gs := gs) hd hn hO

end VerifiableInference.Desc.K1
