-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ReachRounds.lean: ONE STEP BACK ALONG THE VERIFIER's FOLD, WITH
THE LAST STEP's ROUNDS NAMED. `thr_back` (Honest/Thread/ReachBack.lean) hands the library's
`StepYes`, which binds its rounds inside "there are": that they are the run's own is lost there. The
thread's clause (X) (`Thread.Made`, Honest/Thread/Thr.lean) holds the fold over the members in front
AT THE ROUNDS THAT THE PROVER's RUN HAS SEEN. Here that fold is cut one member back (the seal's
`fold_split`, Johnson/Top/H0/Walk/Reach.lean): the last member's step says yes AT THE TAIL OF THESE
ROUNDS, as a term: no "there are" on the rounds. Lemmas; no definition. General in the thread.

  `fold_rest`   on the library's fold: what it leaves over of the rounds is the input's own tail,
     behind as many rounds as the members declare
  `thr_back_rounds`   the thread at b + 1 gives: the chain's first state and the columns as (X)
     binds them; the member number b; the fold over the members in front of it, OVER THE SAME ROUNDS
     AND COLUMNS, with what it leaves over: the state s, the tail of the rounds seen, a rest c of
     the columns; that tail is as long as the member's rounds; and the member's own step from s, at
     that tail and c, to the state at the border
  `thr_back_heard`   the challenges of that tail are the tail of the challenges heard

THE FORM. The fold in front is said with what it leaves over: the form of the premise of the seal's
`fold_snoc`. It is not said as a fold over a front part of the rounds that leaves nothing: that
wants the converse of the seal's `fold_more`, which this file's author has found typed nowhere.

Limits. THE STATE s IS NOT SAID TO BE ONE AT WHICH THE THREAD STOOD AT b. The rest c of the columns
stays under "there is". ONE STEP. None is one of the library's goals. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldBlocks_cons foldBlocks_nil)
open Johnson.Desc.First.Walk.Tied (fold_split)

/-- **What a fold leaves over of the rounds is the input's own tail.** -/
theorem fold_rest {S Cl : Type} (ft : Nat) : ∀ (l : List (Block S Cl)) (s t : S)
    (rs r : List Fmt.RoundView) (cols c : List OpenedColumn), foldBlocks ft l s rs cols = .ok (t, r, c) →
    r = rs.drop (l.flatMap (·.rounds)).length
  | [], s, t, rs, r, cols, c, h => by
    have e := foldBlocks_nil ft s rs cols _ h
    obtain ⟨-, e2⟩ := Prod.mk.inj e
    obtain ⟨rfl, -⟩ := Prod.mk.inj e2
    rfl
  | b :: l, s, t, rs, r, cols, c, h => by
    obtain ⟨s', k, -, -, h'⟩ := foldBlocks_cons ft b l s rs cols _ h
    have ih := fold_rest ft l s' t _ r _ c h'
    rw [List.drop_drop] at ih
    rw [List.flatMap_cons, List.length_append]
    exact ih

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **ONE STEP BACK, WITH ITS ROUNDS NAMED.** -/
theorem thr_back_rounds {b : Nat} {k : Coins Bk} {s' : S} {m : Mid W X} {E : Env}
    (hb : b + 1 ≤ T.bs.length) (hT : Thr T (b + 1) k s' m E) :
    ∃ s₀ cols s blk c, T.begun k m.st.input (m.st.heard.take T.front) s₀ ∧
      T.colsTo (b + 1) m E = .ok cols ∧ T.bs[b]? = some blk ∧
      foldBlocks T.ft (T.bs.take b) s₀ (m.seen.drop T.front) cols =
        .ok (s, m.seen.drop (T.front + roundsTo T.bs b), c) ∧
      (m.seen.drop (T.front + roundsTo T.bs b)).length = blk.rounds.length ∧
      blk.step T.ft s (m.seen.drop (T.front + roundsTo T.bs b)) c = .ok (s', c.length) := by
  unfold Thr at hT
  have hM := hT.2.2.2.2.1
  unfold Thread.Made at hM
  obtain ⟨-, -, -, -, s₀, cols, hbeg, hcols, hf⟩ := hM
  have hblk : T.bs[b]? = some T.bs[b] := List.getElem?_eq_getElem hb
  rw [List.take_add_one, hblk] at hf
  obtain ⟨t, r₁, c₁, h1, h2⟩ := fold_split T.ft _ _ _ _ _ _ hf
  obtain ⟨s'', n, hl, hs, h3⟩ := foldBlocks_cons T.ft T.bs[b] [] t r₁ c₁ _ h2
  have e3 := foldBlocks_nil T.ft s'' _ _ _ h3
  obtain ⟨es, e4⟩ := Prod.mk.inj e3
  obtain ⟨er, ec⟩ := Prod.mk.inj e4
  subst es
  have hlen : r₁.length = T.bs[b].rounds.length := by
    have h5 : (r₁.drop T.bs[b].rounds.length).length = 0 := by
      rw [← er]
      rfl
    rw [List.length_drop] at h5
    rw [List.length_take] at hl
    omega
  rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hs
  have hn : n = c₁.length := by
    have h6 : (c₁.drop n).length = 0 := by
      rw [← ec]
      rfl
    rw [List.length_drop] at h6
    have h7 := (Johnson.Desc.First.Walk.Tied.step_more hs []).1
    omega
  subst hn
  have hr₁ : r₁ = m.seen.drop (T.front + roundsTo T.bs b) := by
    have e := fold_rest T.ft _ _ _ _ _ _ _ h1
    rw [List.drop_drop] at e
    exact e
  subst hr₁
  exact ⟨s₀, cols, t, T.bs[b], c₁, hbeg, hcols, hblk, h1, hlen, hs⟩

/-- **The challenges of that tail are the tail of the challenges heard.** -/
theorem thr_back_heard {b : Nat} {k : Coins Bk} {s' : S} {m : Mid W X} {E : Env}
    (hT : Thr T (b + 1) k s' m E) :
    (m.seen.drop (T.front + roundsTo T.bs b)).map (·.drawn) =
      m.st.heard.drop (T.front + roundsTo T.bs b) := by
  unfold Thr at hT
  have hM := hT.2.2.2.2.1
  unfold Thread.Made at hM
  rw [List.map_drop, hM.1]

end ProofFile.Honest

#print axioms ProofFile.Honest.fold_rest
#print axioms ProofFile.Honest.thr_back_rounds
#print axioms ProofFile.Honest.thr_back_heard
