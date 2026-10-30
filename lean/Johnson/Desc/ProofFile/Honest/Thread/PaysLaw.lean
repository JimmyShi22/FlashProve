-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PaysLaw.lean: from the hypotheses on one sub-protocol
(Honest/Thread/Pays.lean) to the invariant at the border after it (`Thr`, Honest/Thread/Thr.lean).
Conditional lemmas on this folder's own definitions, general in the parameters of a `Thread`.

  1  `mem_fwdStep`, `hear_heard`, `play_heard`   small lemmas: what is open after a row; what `play`
     adds to the challenges heard
  2  `Thread.fits_parts`, `Thread.heard_length`, `Thread.handAt_next`   what the tests on the
     parameters give; how many challenges have been heard at a border; an available tree stays
     available
  3  `thr_next`, `thr_behind`   the invariant after a sub-protocol's acceptance, from the invariant
     before it, the sub-protocol's step and the hypotheses that say nothing of a fall

What these are. They are pointwise: at one input, one run's coins and one list of challenges. Their
hypotheses (the last conjunct of `Plays`, `Behind`, `Exchange`, `RidesPast`, `MadeNext`) are proved
here of no description; `MadeNext` is generic and has to be proved once, not kind by kind.
`Accepted` is not among them: the invariant holds after every acceptance, whether or not an
acceptance has to be proved. They are none of the library's goals, and no goal follows from them
without these hypotheses.

Limits.
  * At an invariant that is false everywhere they say nothing.
  * Hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round, and as many
    challenges as rounds): `thr_next`, `thr_behind`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 Small lemmas -/

/-- What is open after a row is owed by it, or was open before it and is not shut. -/
theorem mem_fwdStep {ι : Type} [DecidableEq ι] {O : List ι} {r : FwdRow ι} {i : ι}
    (h : i ∈ fwdStep O r) : i ∈ r.owes ∨ (i ∈ O ∧ i ∉ r.shuts) := by
  have h' : i ∈ (O.filter fun j => !r.shuts.contains j) ++
      r.owes.filter fun j => !(O.filter fun j' => !r.shuts.contains j').contains j := h
  rcases List.mem_append.1 h' with h1 | h1
  · obtain ⟨a, c⟩ := List.mem_filter.1 h1
    refine Or.inr ⟨a, fun hs => ?_⟩
    simp [hs] at c
  · exact Or.inl (List.mem_filter.1 h1).1

theorem hear_heard {s : Step W X} {x : Told} {d : Fmt.Drawn} {m m' : Mid W X}
    (h : s.hear x d m = .ok m') : m'.st.heard = m.st.heard ++ [d] := by
  unfold Step.hear at h
  cases hm : s.move with
  | none =>
    simp only [hm] at h
    cases h
    rfl
  | some mv =>
    simp only [hm] at h
    split at h
    · cases h
    · cases h
      rfl

/-- After a run of `play` the challenges heard are the earlier ones and the run's own. -/
theorem play_heard : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play ss ds back m = .ok y →
    y.2.st.heard = m.st.heard ++ ds
  | [], [], _, m, y, h => by
    simp only [play] at h
    cases h
    exact (List.append_nil _).symm
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, hm, hz, rfl⟩ := play_cons_ok h
    have a := hear_heard hm
    have b := play_heard ss ds back.tail m' z hz
    show z.2.st.heard = m.st.heard ++ d :: ds
    rw [b, a, List.append_assoc]
    rfl

/-! ## 2 On the parameters -/

variable (T : Thread Bk S Cl V W X Pb)

/-- Two of the tests on the parameters, as propositions. -/
theorem Thread.fits_parts {n : Nat} (h : T.fits n = true) :
    (∀ b, b ≤ n → ∀ σ ∈ T.hand b, T.fixed σ ≤ T.front + roundsTo T.bs b) ∧ T.near ≤ T.front := by
  unfold Thread.fits at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨-, h4⟩, h5⟩ := h
  refine ⟨fun b hb σ hσ => ?_, of_decide_eq_true h5⟩
  have h' := List.all_eq_true.1 h4 b (List.mem_range.2 (Nat.lt_succ_of_le hb))
  exact of_decide_eq_true (List.all_eq_true.1 h' σ hσ)

/-- (F) counts the challenges heard. -/
theorem Thread.heard_length {b : Nat} {m : Mid W X} (h : T.Fit b m) :
    m.st.heard.length = T.front + roundsTo T.bs b := by
  have e := drawsFit_length _ _ h
  rw [List.length_append] at e
  exact e

/-- A tree that is available, and fixed by the challenges heard, stays available after further
rounds, if the input is unchanged, the new challenges are appended to those heard, and the available
tables are tight (`Env.Tight`). -/
theorem Thread.handAt_next {σ : Fmt.TreeSource} {k : Coins Bk} {m m' : Mid W X} {E : Env}
    {ps : List Played} {ds : List Fmt.Drawn} (hi : m'.st.input = m.st.input)
    (hh : m'.st.heard = m.st.heard ++ ds) (hx : T.fixed σ ≤ m.st.heard.length) (hE : E.Tight)
    (h : T.handAt σ k m E = true) : T.handAt σ k m' (E.add ps) = true := by
  have et : T.tableAt σ k m' = T.tableAt σ k m := by
    unfold Thread.tableAt
    rw [hi, hh, List.take_append_of_le_length hx]
  have ee : (E.add ps).tree σ = E.tree σ := by
    cases σ with
    | taken ch j => rfl
    | own j =>
      show (if j < E.sent then E.tree (.own j) else ((tablesOf ps)[j - E.sent]?).bind id) =
        E.tree (.own j)
      by_cases hj : j < E.sent
      · rw [if_pos hj]
      · exfalso
        have hn := hE j (Nat.le_of_not_lt hj)
        unfold Thread.handAt at h
        rw [hn] at h
        simp at h
  unfold Thread.handAt at h ⊢
  rw [ee, et]
  exact h

/-! ## 3 The invariant after a sub-protocol -/

/-- **The invariant after a sub-protocol.** A conditional lemma on this folder's own definitions:
from the invariant before it, the sub-protocol's step, what has to be proved of the sub-protocol
itself after the step (its new trees, the form, the riders, `keeps`), and the three hypotheses
`Exchange`, `RidesPast` and `MadeNext`; and the parameters have to pass `Thread.fits n`, with b
below n. It is none of the library's goals. -/
theorem thr_next {n b : Nat} {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hfit : T.fits n = true) (hb : b < n) (hblk : T.bs[b]? = some blk) (hA : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s')
    (hT : T.Trees (T.fresh b) k y.2 (E.add y.1)) (hF : T.Form (b + 1) k s' y.2)
    (hRd : T.rides (b + 1) y.2.st.input s') (hK : T.keeps b s s') (hX : Exchange T b)
    (hR : RidesPast T b) (hM : MadeNext T b) : Thr T (b + 1) k s' y.2 (E.add y.1) := by
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨hH0, hF0, -, hI0, hM0, -, hV0⟩ := hA'
  unfold Thread.Hand at hH0
  obtain ⟨hSt, hTr⟩ := hH0
  have hM0' := hM0
  unfold Thread.Made at hM0'
  obtain ⟨-, -, -, hTi, -⟩ := hM0'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  obtain ⟨hfx, -⟩ := T.fits_parts hfit
  obtain ⟨hF1, hM1⟩ := hM blk hblk k s m E ds y cols s' hF0 hM0 hd hS
  have hfr : T.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  have es : T.seat k y.2 s' = T.seat k m s' := by
    unfold Thread.seat
    rw [ei, eh, List.take_append_of_le_length hfr]
  unfold Thr
  refine ⟨?_, hF1, hF, ?_, hM1, hRd, ?_⟩
  · unfold Thread.Hand
    refine ⟨?_, ?_⟩
    · intro i x
      show E.stored i x = T.stored y.2.st.input i x
      rw [ei]
      exact hSt i x
    · intro σ hσ
      by_cases ho : σ ∈ T.hand b
      · refine T.handAt_next ei eh ?_ hTi (hTr σ ho)
        rw [hlen]
        exact hfx b (Nat.le_of_lt hb) σ ho
      · have hm : σ ∈ T.fresh b := List.mem_filter.2 ⟨hσ, by simp [ho]⟩
        exact hT σ hm
  · intro ds' i hi
    by_cases ho : i ∈ (T.row b).owes
    · exact hX blk hblk k s m E ds y cols s' hA hd hS ds' i ho
    · have hi' : i ∈ fwdStep (T.opened b) (T.row b) := hi
      rcases mem_fwdStep hi' with h1 | ⟨h1, h2⟩
      · exact absurd h1 ho
      · have h0 := hI0 (ds ++ ds') i h1
        have h3 := hR k s m E s' y.1 i _ hA hK h1 h2 ho h0
        rw [es, ei, eh, List.append_assoc]
        exact h3
  · rw [ei]
    exact hV0

/-- **The same, with `Behind` as one hypothesis.** A conditional lemma on this folder's own
definitions. It is none of the library's goals. -/
theorem thr_behind {n b : Nat} {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hfit : T.fits n = true) (hb : b < n) (hblk : T.bs[b]? = some blk) (hA : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s')
    (hT : T.Trees (T.fresh b) k y.2 (E.add y.1)) (hB : Behind T b) (hX : Exchange T b)
    (hR : RidesPast T b) (hM : MadeNext T b) : Thr T (b + 1) k s' y.2 (E.add y.1) := by
  obtain ⟨hF, hRd, hK⟩ := hB blk hblk k s m E ds y cols s' hA hd hS
  exact thr_next T hfit hb hblk hA hd hS hT hF hRd hK hX hR hM

end ProofFile.Honest

#print axioms ProofFile.Honest.mem_fwdStep
#print axioms ProofFile.Honest.hear_heard
#print axioms ProofFile.Honest.play_heard
#print axioms ProofFile.Honest.Thread.fits_parts
#print axioms ProofFile.Honest.Thread.heard_length
#print axioms ProofFile.Honest.Thread.handAt_next
#print axioms ProofFile.Honest.thr_next
#print axioms ProofFile.Honest.thr_behind
