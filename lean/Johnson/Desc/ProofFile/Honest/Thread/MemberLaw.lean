-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/MemberLaw.lean: from clause (X) of the invariant: an earlier
sub-protocol's own step. At a border b of a `Thread` (Honest/Thread/Thr.lean) and a sub-protocol j
before it: that sub-protocol's own step has accepted, at some state, on rounds whose challenges are
that sub-protocol's own slice of what the prover's run has heard; and the fold over the
sub-protocols between it and the border leads from the state after that acceptance to the state at
the border. With the rule by which a condition that every sub-protocol's acceptance keeps is carried
along such a fold. Lemmas on the format's own fold and this folder's definitions, general in the
parameters of the `Thread`: no kind is named.

What it is for. No clause of the invariant says outright that a field of the verifier's state is a
function of what was heard: only (X) ties the state to the rounds, as a fold. A kind's author who
needs such a statement gets it in three steps: `made_member` (here); a lemma of their own "my
decision sets this field to that function of its own rounds' challenges"; `fold_keeps` (here) over
"no later sub-protocol changes that field".

  1  `fold_member`, `fold_keeps`   on the fold
  2  `made_member`   at the `Thread`

Limits.
  * It is none of the library's goals.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl : Type}

/-! ## 1 On the fold -/

theorem roundsTo_cons (b : Block S Cl) (l : List (Block S Cl)) (j : Nat) :
    roundsTo (b :: l) (j + 1) = b.rounds.length + roundsTo l j := by
  unfold roundsTo declsTo
  rw [List.take_succ_cons, List.flatMap_cons, List.length_append]

/-- **Inside a fold that returns**: sub-protocol number j: its own step accepts, at some state, on
its own stretch of the rounds; and the fold over the sub-protocols after it leads from there to
the end. -/
theorem fold_member (ft : Nat) : ∀ (bs : List (Block S Cl)) (j : Nat) (blk : Block S Cl),
    bs[j]? = some blk → ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
      (out : S × List Fmt.RoundView × List OpenedColumn), foldBlocks ft bs s rs cols = .ok out →
    ∃ (sj sj' : S) (c : List OpenedColumn) (n : Nat) (rs' : List Fmt.RoundView) (c' : List OpenedColumn),
      blk.step ft sj ((rs.drop (roundsTo bs j)).take blk.rounds.length) c = .ok (sj', n) ∧
        foldBlocks ft (bs.drop (j + 1)) sj' rs' c' = .ok out
  | [], _, _, hj, _, _, _, _, _ => by cases hj
  | b :: l, 0, blk, hj, s, rs, cols, out, h => by
    cases Option.some.inj hj
    obtain ⟨s', k, -, hs, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    exact ⟨s, s', cols, k, _, _, hs, h'⟩
  | b :: l, j + 1, blk, hj, s, rs, cols, out, h => by
    obtain ⟨s', k, -, -, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    obtain ⟨sj, sj', c, n, rs', c', hs, ht⟩ := fold_member ft l j blk hj s' _ _ out h'
    refine ⟨sj, sj', c, n, rs', c', ?_, ht⟩
    rw [roundsTo_cons, ← List.drop_drop]
    exact hs

/-- **What every sub-protocol's acceptance keeps is carried along a fold.** -/
theorem fold_keeps (ft : Nat) (Q : S → Prop) : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, ∀ s rs c s' n, b.step ft s rs c = .ok (s', n) → Q s → Q s') →
    ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs cols = .ok out → Q s → Q out.1
  | [], _, s, rs, cols, out, h, hq => by
    rw [foldBlocks_nil ft s rs cols out h]
    exact hq
  | b :: l, hk, s, rs, cols, out, h, hq => by
    obtain ⟨s', k, -, hs, h'⟩ := foldBlocks_cons ft b l s rs cols out h
    exact fold_keeps ft Q l (fun x hx => hk x (List.mem_cons_of_mem _ hx)) s' _ _ out h'
      (hk b (List.mem_cons_self ..) s _ _ s' k hs hq)

/-! ## 2 At the `Thread` -/

variable {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **From (X): an earlier sub-protocol's own step**, on rounds whose challenges are its own slice
of what was heard. A lemma on the format's fold and the frame's definitions. It is none of the
library's goals. -/
theorem made_member {b j : Nat} {blk : Block S Cl} (hj : j < b) (hblk : T.bs[j]? = some blk)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hM : T.Made b k s m E) :
    ∃ (sj sj' : S) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat) (rs' : List Fmt.RoundView)
      (c' : List OpenedColumn), blk.step T.ft sj rs c = .ok (sj', n) ∧
        rs.map (·.drawn) = heardFrom m.st (T.front + roundsTo T.bs j) blk.rounds.length ∧
        foldBlocks T.ft ((T.bs.take b).drop (j + 1)) sj' rs' c' = .ok (s, [], []) := by
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, -, -, hf⟩ := hM
  have hb' : (T.bs.take b)[j]? = some blk := by
    rw [List.getElem?_take_of_lt hj]
    exact hblk
  obtain ⟨sj, sj', c, n, rs', c', hs, ht⟩ := fold_member T.ft _ j blk hb' _ _ _ _ hf
  refine ⟨sj, sj', _, c, n, rs', c', hs, ?_, ht⟩
  have er : roundsTo (T.bs.take b) j = roundsTo T.bs j := by
    unfold roundsTo declsTo
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold heardFrom
  rw [er, List.map_take, List.map_drop, List.map_drop, hseen, List.drop_drop]

end ProofFile.Honest

#print axioms ProofFile.Honest.roundsTo_cons
#print axioms ProofFile.Honest.fold_member
#print axioms ProofFile.Honest.fold_keeps
#print axioms ProofFile.Honest.made_member
