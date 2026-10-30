-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/MemberFrom.lean: `fold_member` and `made_member`
(Honest/Thread/MemberLaw.lean) with one clause more: whence the state in front of the earlier
sub-protocol comes. `made_member` hands out, at a border b of a `Thread` and a sub-protocol j before
it, a state at which that sub-protocol's own step accepts, on rounds whose challenges are its own
slice of what was heard. It does not say that this state is the one that the fold over the
sub-protocols before j leads to. Here the same state is bound once for all clauses: the fold over
the first j sub-protocols leads to it from a first state that `begun` allows, and leaves the rounds
and the columns at which the step is then taken. Lemmas on the format's own fold and this folder's
definitions, general in the parameters of the `Thread`: no kind is named.

What it is for. A kind's author whose lemma on their own decision asks something of the state in
front that holds of reached states alone (an invariant of the verifier's run) gets that state as a
reached one: `made_member_reach` gives the library's own `Reach` (Johnson/Top/H0/Walk/Reach.lean) at
j for it, beside the step's acceptance and the tie of the rounds.

  1  `fold_member_from`   on the fold
  2  `made_member_from`, `made_member_reach`   at the `Thread`

Limits.
  * Nothing here says that `Thread.Made` holds at any state.
  * `made_member_reach` takes the premise of `reach_of_made` (Honest/Thread/MadeLaw.lean): `start z`
    is the only first state that `begun` allows.
  * It is none of the library's goals.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MemberLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)

variable {S Cl : Type}

/-! ## 1 On the fold -/

/-- **`fold_member`, and whence the state in front comes**: the fold over the sub-protocols before
number j leads from the start to the state at which number j's own step accepts, and leaves the
rounds and the columns at which that step is taken. -/
theorem fold_member_from (ft : Nat) : ∀ (bs : List (Block S Cl)) (j : Nat) (blk : Block S Cl),
    bs[j]? = some blk → ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (out : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft bs s rs cols = .ok out →
    ∃ (sj sj' : S) (c : List OpenedColumn) (n : Nat) (rs' : List Fmt.RoundView) (c' : List OpenedColumn),
      foldBlocks ft (bs.take j) s rs cols = .ok (sj, rs.drop (roundsTo bs j), c) ∧
      blk.step ft sj ((rs.drop (roundsTo bs j)).take blk.rounds.length) c = .ok (sj', n) ∧
        foldBlocks ft (bs.drop (j + 1)) sj' rs' c' = .ok out
  | [], _, _, hj, _, _, _, _, _ => by cases hj
  | b :: l, 0, blk, hj, s, rs, cols, out, h => by
    cases Option.some.inj hj
    obtain ⟨s', k, -, hs, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    refine ⟨s, s', cols, k, _, _, ?_, hs, h'⟩
    have e0 : roundsTo (b :: l) 0 = 0 := by
      unfold roundsTo declsTo
      rw [List.take_zero]
      rfl
    rw [e0, List.drop_zero, List.take_zero]
    unfold foldBlocks
    rfl
  | b :: l, j + 1, blk, hj, s, rs, cols, out, h => by
    obtain ⟨s', k, hl, hb, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    obtain ⟨sj, sj', c, n, rs', c', hf, hs, ht⟩ := fold_member_from ft l j blk hj s' _ _ out h'
    refine ⟨sj, sj', c, n, rs', c', ?_, ?_, ht⟩
    · rw [List.take_succ_cons, roundsTo_cons, ← List.drop_drop]
      exact foldBlocks_cons_ok.2 ⟨hl, s', k, hb, hf⟩
    · rw [roundsTo_cons, ← List.drop_drop]
      exact hs

/-! ## 2 At the `Thread` -/

variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **`made_member`, and whence the state in front comes.** One state `sj` for all clauses: the fold
over the first j sub-protocols leads to it from a first state that `begun` allows; the step of
sub-protocol j accepts at it, on the first rounds and at the columns that this fold leaves. A lemma
on the format's fold and the frame's definitions. It is none of the library's goals. -/
theorem made_member_from {b j : Nat} {blk : Block S Cl} (hj : j < b) (hblk : T.bs[j]? = some blk)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hM : T.Made b k s m E) :
    ∃ (s₀ sj sj' : S) (cols : List OpenedColumn) (rs₀ rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat)
      (rs' : List Fmt.RoundView) (c' : List OpenedColumn),
        T.begun k m.st.input (m.st.heard.take T.front) s₀ ∧
        foldBlocks T.ft (T.bs.take j) s₀ (m.seen.drop T.front) cols = .ok (sj, rs₀, c) ∧
        rs = rs₀.take blk.rounds.length ∧
        blk.step T.ft sj rs c = .ok (sj', n) ∧
        rs.map (·.drawn) = heardFrom m.st (T.front + roundsTo T.bs j) blk.rounds.length ∧
        foldBlocks T.ft ((T.bs.take b).drop (j + 1)) sj' rs' c' = .ok (s, [], []) := by
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hf⟩ := hM
  have hb' : (T.bs.take b)[j]? = some blk := by
    rw [List.getElem?_take_of_lt hj]
    exact hblk
  obtain ⟨sj, sj', c, n, rs', c', hfr, hs, ht⟩ := fold_member_from T.ft _ j blk hb' _ _ _ _ hf
  have et : (T.bs.take b).take j = T.bs.take j := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have er : roundsTo (T.bs.take b) j = roundsTo T.bs j := by
    unfold roundsTo declsTo
    rw [et]
  rw [et] at hfr
  refine ⟨s₀, sj, sj', cols, _, _, c, n, rs', c', hbeg, hfr, rfl, hs, ?_, ht⟩
  unfold heardFrom
  rw [er, List.map_take, List.map_drop, List.map_drop, hseen, List.drop_drop]

/-- **The state in front is reached**, in the library's own sense, under the premise of
`reach_of_made`; beside it the three clauses of `made_member`, at that same state. -/
theorem made_member_reach {P : Type} (start : P → S) (z : P) {b j : Nat} {blk : Block S Cl}
    (hj : j < b) (hb : b ≤ T.bs.length) (hblk : T.bs[j]? = some blk)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = start z)
    (hM : T.Made b k s m E) :
    ∃ (sj sj' : S) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (rs' : List Fmt.RoundView)
      (c' : List OpenedColumn), Reach T.ft T.bs start j (z, sj) ∧
        blk.step T.ft sj rs c = .ok (sj', n) ∧
        rs.map (·.drawn) = heardFrom m.st (T.front + roundsTo T.bs j) blk.rounds.length ∧
        foldBlocks T.ft ((T.bs.take b).drop (j + 1)) sj' rs' c' = .ok (s, [], []) := by
  obtain ⟨s₀, sj, sj', cols, rs₀, rs, c, n, rs', c', hbeg, hfr, -, hs, hh, ht⟩ :=
    made_member_from T hj hblk hM
  rw [h0 s₀ hbeg] at hfr
  exact ⟨sj, sj', rs, c, n, rs', c',
    reach_of_fold j (Nat.le_trans (Nat.le_of_lt hj) hb) sj _ _ _ _ hfr, hs, hh, ht⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.fold_member_from
#print axioms ProofFile.Honest.made_member_from
#print axioms ProofFile.Honest.made_member_reach
