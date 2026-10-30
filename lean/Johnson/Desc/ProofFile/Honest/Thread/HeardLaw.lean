-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/HeardLaw.lean: which of the challenges heard a sub-protocol's
rounds drew. Three small lemmas on the frame's own definitions, general in the parameters of the
`Thread`: no kind is named.

  `heardFrom_member`   the rounds that a sub-protocol's step is given drew the entries of
     `State.heard` from the number (the rounds before the chain + the chain's rounds before the
     sub-protocol) on
  `heardFrom_more`   these entries stay at every later state, once all of them have been heard
  `roundsTo_inFront`   its second summand, where `roundsInFront` returns one, in the two forms in
     which it is written (`roundsInFront`, Honest/ForKinds.lean; `roundsTo` at `borderNo`,
     Honest/Thread/Thr.lean)

What they are for. A part of a later sub-protocol that needs a challenge of an earlier one takes it
by `heardFrom` (Honest/ForKinds.lean) at a number that is public data; the verifier's definition
took it from the rounds that it was given. These lemmas together give that the two are one list.

Limits.
  * They are none of the library's goals.
  * Among the hypotheses that the prose above does not name: `T.Fit b m` (clause (F) at the border,
    at the state before the step), `T.Moved` (the step's rounds are played; the entries are read at
    the state after them) and `drawsFit` (`drawFit` round by round, and as many challenges as
    rounds): `heardFrom_member`; `i + n` is at most `t.heard.length` (all `n` entries have been
    heard at the earlier state): `heardFrom_more`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- The entries stay where what is heard grows, if all `n` have been heard. -/
theorem heardFrom_more {t t' : State W X} {more : List Fmt.Drawn} {i n : Nat}
    (h : t'.heard = t.heard ++ more) (hi : i + n ≤ t.heard.length) :
    heardFrom t' i n = heardFrom t i n := by
  unfold heardFrom
  rw [h, List.drop_append_of_le_length (Nat.le_trans (Nat.le_add_right i n) hi),
    List.take_append_of_le_length]
  rw [List.length_drop]
  omega

/-- The two forms of "the chain's rounds before the sub-protocol at a place". -/
theorem roundsTo_inFront : ∀ (bs : List (Block S Cl)) (a : Place) (n : Nat),
    roundsInFront bs a = some n → roundsTo bs (borderNo bs a) = n
  | [], _, _, h => by simp [roundsInFront] at h
  | b :: bs, a, n, h => by
    unfold roundsInFront at h
    by_cases hp : (b.place == a) = true
    · rw [if_pos hp] at h
      have e : borderNo (b :: bs) a = 0 := by simp [borderNo, List.findIdx_cons, hp]
      rw [e]
      exact Option.some.inj h
    · rw [if_neg hp] at h
      obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.1 h
      have e : borderNo (b :: bs) a = borderNo bs a + 1 := by
        simp [borderNo, List.findIdx_cons, hp]
      have ih := roundsTo_inFront bs a n' hn'
      rw [e]
      unfold roundsTo declsTo at ih ⊢
      rw [List.take_succ_cons, List.flatMap_cons, List.length_append, ih, Nat.add_comm]

/-- **The rounds that a sub-protocol's step is given drew these entries of what was heard.** -/
theorem heardFrom_member (T : Thread Bk S Cl V W X Pb) {b : Nat} {blk : Block S Cl}
    {k : Coins Bk} {m : Mid W X} {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X}
    {cols : List OpenedColumn} (hF : T.Fit b m) (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m E ds y cols) :
    heardFrom y.2.st (T.front + roundsTo T.bs b) blk.rounds.length =
      (roundsOf y.1).map (·.drawn) := by
  unfold Thread.Moved at hM
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have eh := play_heard _ _ _ _ _ hy
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)
  have hlen := T.heard_length hF
  unfold heardFrom
  rw [eh, List.drop_left' hlen, hdr, ← drawsFit_length _ _ hd, List.take_length]

end ProofFile.Honest

#print axioms ProofFile.Honest.heardFrom_more
#print axioms ProofFile.Honest.roundsTo_inFront
#print axioms ProofFile.Honest.heardFrom_member
