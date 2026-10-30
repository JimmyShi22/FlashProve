-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/HandNext.lean: WHAT IS KNOWN OF THE STATE BEHIND A SUB-PROTOCOL
WHOSE ROUNDS WERE PLAYED, WITHOUT ITS ACCEPTANCE. `SaidNext` (Honest/Thread/Said.lean) hands its
filler `Thr` in front of a sub-protocol, what is said there, and `Thread.Moved`. It hands no
acceptance, so `thr_next_at` (Honest/Thread/PaysS.lean) does not apply. A letter that reads the
clause `Thread.Hand` behind the sub-protocol needs that clause from `Thread.Moved` alone.

  `trees_at_y`   the last clause of `PlaysS`, at the very play that `Thread.Moved` names
  `Thread.hand_next`   `Thread.Hand` behind the sub-protocol, from `Thr` in front of it,
    `Thread.Moved` and the sub-protocol's own new trees
  `Thread.trees_of_fresh_nil`   where a sub-protocol has no new tree, nothing is asked of its trees

What these are. Conditional lemmas on our own definitions. None is one of the library's goals. The
lines of `Thread.hand_next`'s proof are those of `thr_next_at`'s on the same clause, with `b ≤ n`
for `b < n`.

Limits.
  * `trees_at_y`'s premise `hP` is a universal statement of which the conclusion is one instance.
    The lemma says only that the play of `Thread.Moved` is the play of `PlaysS`. It adds nothing
    where `PlaysS` is not already had.
  * `hst` stays a premise: no stop is among the hypotheses of `SaidNext`.
  * `Thread.Moved` holds only where `play` returns. Where no play returns these lemmas say nothing.
  * Nothing here shows that the invariant holds at any state of a run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.ThrField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-- **The last clause of `PlaysS`, at the play that `Thread.Moved` names.** -/
theorem trees_at_y {b : Nat} {blk : Block S Cl} (hblk : T.bs[b]? = some blk)
    (hP : PlaysS T Said b) {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hA : Thr T b k s m E) (hS : Said b k m) (hd : drawsFit blk.rounds ds = true)
    (hst : chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none)
    (hM : T.Moved blk k m E ds y cols) :
    T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hM
  obtain ⟨y', cols', hM', hT'⟩ := hP blk hblk k s m E ds l ⟨hA, hS⟩ hd hst hl
  obtain ⟨⟨l', hl', hy'⟩, -⟩ := hM'
  rw [hl] at hl'
  cases hl'
  rw [hy] at hy'
  cases hy'
  exact hT'

/-- **`Thread.Hand` behind a sub-protocol**, from `Thr` in front of it, `Thread.Moved` and its new
trees. No acceptance is among the premises. -/
theorem Thread.hand_next {n b : Nat} {blk : Block S Cl} (hfit : T.fits n = true) (hb : b ≤ n)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hA : Thr T b k s m E) (hM : T.Moved blk k m E ds y cols)
    (hT : T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    T.Hand (b + 1) k (y.2.took cols) (E.add y.1) := by
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨hH0, hF0, -, -, hM0, -, -⟩ := hA'
  unfold Thread.Hand at hH0
  obtain ⟨hSt, hTr⟩ := hH0
  have hM0' := hM0
  unfold Thread.Made at hM0'
  obtain ⟨-, -, -, hTi, -⟩ := hM0'
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  obtain ⟨hfx, -⟩ := T.fits_parts hfit
  refine (hand_took T (b + 1) k y.2 (E.add y.1) cols).2 ?_
  unfold Thread.Hand
  refine ⟨?_, ?_⟩
  · intro i x
    show E.stored i x = T.stored y.2.st.input i x
    rw [ei]
    exact hSt i x
  · intro σ hσ
    by_cases ho : σ ∈ T.hand b
    · refine T.handAt_next ei eh ?_ hTi (hTr σ ho)
      rw [hlen]
      exact hfx b hb σ ho
    · have hm : σ ∈ T.fresh b := List.mem_filter.2 ⟨hσ, by simp [ho]⟩
      exact hT σ hm

/-- Where a sub-protocol has no new tree, `Thread.Trees` asks nothing of it. -/
theorem Thread.trees_of_fresh_nil {b : Nat} (h : T.fresh b = []) (k : Coins Bk) (m : Mid W X)
    (E : Env) : T.Trees (T.fresh b) k m E := by
  rw [h]
  intro σ hσ
  cases hσ

end ProofFile.Honest

#print axioms ProofFile.Honest.trees_at_y
#print axioms ProofFile.Honest.Thread.hand_next
#print axioms ProofFile.Honest.Thread.trees_of_fresh_nil
