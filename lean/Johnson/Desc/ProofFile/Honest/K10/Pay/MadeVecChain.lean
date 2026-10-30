-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeVecChain.lean: from the thread's clause on the verifier's own fold (`Thread.Made`, Honest/Thread/Thr.lean) at a border: every
earlier sub-protocol's own step, with ONE first state and ONE list of columns for all of them. So the state behind number j and
the state in front of number j + 1 are one state: both are the value of one fold. General in the thread.

  `fold_two`       inside a fold that returns: the fold over the first j, number j's own step, the fold over the first j + 1
  `take_le`, `roundsTo_take`   a beginning of a beginning
  **`made_cuts`**   at the thread; each member's rounds draw its own slice of what was heard
  `cut_meets`      two returns of one fold are one

Kin: `made_member`, `made_member_from` (Honest/Thread/MemberLaw.lean, MemberFrom.lean) bind the states and the columns anew at
each call, so two calls cannot be joined.

Limits. Lemmas on the format's fold and the frame's definitions. Nothing on a prover's moves.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MemberFrom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc

variable {S Cl : Type}

/-- Inside a fold that returns: the fold over the first j sub-protocols, number j's own step, and the
fold over the first j + 1. -/
theorem fold_two (ft : Nat) : ∀ (bs : List (Block S Cl)) (j : Nat) (blk : Block S Cl),
    bs[j]? = some blk → ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (out : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft bs s rs cols = .ok out →
    ∃ (sj sj' : S) (c : List OpenedColumn) (n : Nat),
      foldBlocks ft (bs.take j) s rs cols = .ok (sj, rs.drop (roundsTo bs j), c) ∧
      blk.step ft sj ((rs.drop (roundsTo bs j)).take blk.rounds.length) c = .ok (sj', n) ∧
      foldBlocks ft (bs.take (j + 1)) s rs cols =
        .ok (sj', rs.drop (roundsTo bs (j + 1)), c.drop n)
  | [], _, _, hj, _, _, _, _, _ => by cases hj
  | b :: l, 0, blk, hj, s, rs, cols, out, h => by
    cases Option.some.inj hj
    obtain ⟨s', k, hl, hs, -⟩ := foldBlocks_cons ft b l s rs cols out h
    have e0 : roundsTo (b :: l) 0 = 0 := by
      unfold roundsTo declsTo
      rw [List.take_zero]
      rfl
    have e0' : roundsTo l 0 = 0 := by
      unfold roundsTo declsTo
      rw [List.take_zero]
      rfl
    refine ⟨s, s', cols, k, ?_, hs, ?_⟩
    · rw [e0, List.drop_zero, List.take_zero]
      unfold foldBlocks
      rfl
    · rw [List.take_succ_cons, List.take_zero, roundsTo_cons, e0', Nat.add_zero]
      refine foldBlocks_cons_ok.2 ⟨hl, s', k, hs, ?_⟩
      unfold foldBlocks
      rfl
  | b :: l, j + 1, blk, hj, s, rs, cols, out, h => by
    obtain ⟨s', k, hl, hb, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    obtain ⟨sj, sj', c, n, hf, hs, hg⟩ := fold_two ft l j blk hj s' _ _ out h'
    refine ⟨sj, sj', c, n, ?_, ?_, ?_⟩
    · rw [List.take_succ_cons, roundsTo_cons, ← List.drop_drop]
      exact foldBlocks_cons_ok.2 ⟨hl, s', k, hb, hf⟩
    · rw [roundsTo_cons, ← List.drop_drop]
      exact hs
    · rw [List.take_succ_cons, roundsTo_cons, ← List.drop_drop]
      exact foldBlocks_cons_ok.2 ⟨hl, s', k, hb, hg⟩

theorem take_le {α : Type} (l : List α) {j B : Nat} (h : j ≤ B) : (l.take B).take j = l.take j := by
  rw [List.take_take, Nat.min_eq_left h]

theorem roundsTo_take (bs : List (Block S Cl)) {j B : Nat} (h : j ≤ B) :
    roundsTo (bs.take B) j = roundsTo bs j := by
  unfold roundsTo declsTo
  rw [take_le bs h]

/-- Two returns of one fold are one. -/
theorem cut_meets {α : Type} {x : Except String α} {a b : α} (h : x = .ok a) (g : x = .ok b) :
    a = b := Except.ok.inj (h.symm.trans g)

variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **From the verifier's fold at a border: every earlier sub-protocol's own step, at one first state
and one list of columns.** -/
theorem made_cuts {B : Nat} {k : Coins Bk} {sB : S} {m : Mid W X} {E : Env}
    (hM : T.Made B k sB m E) :
    ∃ (s₀ : S) (cols : List OpenedColumn), T.begun k m.st.input (m.st.heard.take T.front) s₀ ∧
      ∀ (j : Nat) (blk : Block S Cl), j < B → T.bs[j]? = some blk →
        ∃ (sj sj' : S) (c : List OpenedColumn) (n : Nat),
          foldBlocks T.ft (T.bs.take j) s₀ (m.seen.drop T.front) cols =
            .ok (sj, (m.seen.drop T.front).drop (roundsTo T.bs j), c) ∧
          blk.step T.ft sj
            (((m.seen.drop T.front).drop (roundsTo T.bs j)).take blk.rounds.length) c =
            .ok (sj', n) ∧
          foldBlocks T.ft (T.bs.take (j + 1)) s₀ (m.seen.drop T.front) cols =
            .ok (sj', (m.seen.drop T.front).drop (roundsTo T.bs (j + 1)), c.drop n) ∧
          (((m.seen.drop T.front).drop (roundsTo T.bs j)).take blk.rounds.length).map (·.drawn) =
            heardFrom m.st (T.front + roundsTo T.bs j) blk.rounds.length := by
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hf⟩ := hM
  refine ⟨s₀, cols, hbeg, fun j blk hj hblk => ?_⟩
  have hb' : (T.bs.take B)[j]? = some blk := by
    rw [List.getElem?_take_of_lt hj]
    exact hblk
  obtain ⟨sj, sj', c, n, h1, h2, h3⟩ := fold_two T.ft _ j blk hb' _ _ _ _ hf
  rw [take_le T.bs (Nat.le_of_lt hj), roundsTo_take T.bs (Nat.le_of_lt hj)] at h1
  rw [roundsTo_take T.bs (Nat.le_of_lt hj)] at h2
  rw [take_le T.bs hj, roundsTo_take T.bs hj] at h3
  refine ⟨sj, sj', c, n, h1, h2, h3, ?_⟩
  unfold heardFrom
  rw [List.map_take, List.map_drop, List.map_drop, hseen, List.drop_drop]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.fold_two
#print axioms ProofFile.Honest.K10.take_le
#print axioms ProofFile.Honest.K10.roundsTo_take
#print axioms ProofFile.Honest.K10.cut_meets
#print axioms ProofFile.Honest.K10.made_cuts
