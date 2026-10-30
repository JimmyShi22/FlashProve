-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Inner.lean: the proofs of `HeadMergeFront` and
`HeadMergeInnerPlayed` (Honest/K11/Plays/InnerStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The frame's test on challenges, taken apart at the first round and at the others
(`plain_of_fit`); from it the call's own test (`drawsOk_of_fit`, Honest/SumLaw/More.lean); the part
played alone: `headMergeAlone` (Honest/K11/Plays/Proofs.lean). The second statement is the law
itself (`headMergeInner`, Honest/K11/Inner/Whole.lean), handed these eight: that Lean takes the term
shows that `InnerTail` is that law's own text.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.InnerStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Proofs
import Johnson.Desc.ProofFile.Honest.K11.Inner.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim RoundName)
open VerifiableInference.Desc.Part.MaskedSum (entries)
open Johnson.Desc.First.ForkMerge (HeadMergeP mergeEntries)
open ProofFile.Honest.SumLaw (drawsOk drawsOk_of_fit)

/-- Challenges that fit rounds which draw no position and no matrix entry hold none. -/
theorem plain_of_fit : ∀ (rs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn), drawsFit rs ds = true →
    (∀ r ∈ rs, r.entry.poss = 0 ∧ r.entry.trits = 0) → ∀ d ∈ ds, d.poss = [] ∧ d.trits = []
  | [], [], _, _ => fun _ hd => nomatch hd
  | r :: rs, d :: ds, h, hr => by
    have h' : (drawFit r d && drawsFit rs ds) = true := h
    rw [Bool.and_eq_true] at h'
    have h1 := h'.1
    unfold drawFit at h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨e1, e2⟩ := hr r List.mem_cons_self
    intro d' hd'
    rcases List.mem_cons.1 hd' with rfl | hm
    · exact ⟨List.length_eq_zero_iff.1 (by rw [h1.1.1.1.1.1.1.2, e1]),
        List.length_eq_zero_iff.1 (by rw [h1.1.1.1.1.1.2, e2])⟩
    · exact plain_of_fit rs ds h'.2 (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')) d' hm
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h

/-- The merge's rounds draw no position and no matrix entry. -/
theorem merge_plain (lk work : Nat) :
    ∀ r ∈ (mergeEntries lk 1 work).map (fun e => ({ entry := e } : Fmt.DeclaredRound)),
      r.entry.poss = 0 ∧ r.entry.trits = 0 := by
  intro r hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr
  simp only [mergeEntries, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | ⟨_, rfl⟩ | rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- The sumcheck's rounds draw as many elements as the call's own entries state. -/
theorem sumEntries_draws (lk work : Nat) :
    ((sumEntries lk work).map fun e => ({ entry := e } : Fmt.DeclaredRound)).map (·.entry.drawE) =
      (entries (headMergeShape lk)).map (·.drawE) := by
  simp [sumEntries, mergeEntries, entries, headMergeShape,
    VerifiableInference.Desc.Part.MaskedSum.entry, List.map_replicate]

/-- **Where the row is played the law's first eight premises hold.** -/
theorem headMergeFront : HeadMergeFront := by
  intro W₀ Rc Xi Tr X P claims weights c d₀ ds m hd
  have hall := plain_of_fit _ _ hd (merge_plain P.lay.lk P.work)
  have hd' : (drawFit
      { entry := { name := RoundName.batSigma.name, work := P.work, drawE := 1, rows := 1 } } d₀ &&
      drawsFit ((sumEntries P.lay.lk P.work).map fun e => { entry := e }) ds) = true := hd
  rw [Bool.and_eq_true] at hd'
  have h1 := hd'.1
  unfold drawFit at h1
  simp only [Bool.and_eq_true, beq_iff_eq] at h1
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 h1.1.1.1.1.1.1.1
  obtain ⟨p0, t0⟩ := hall d₀ List.mem_cons_self
  refine ⟨x, rfl, hx, p0, t0, ?_, ?_, fun d hm => hall d (List.mem_cons_of_mem _ hm),
    headMergeAlone W₀ Rc Xi Tr X P claims weights c d₀ ds m hd⟩
  · show (m.st.heard ++ [d₀]).getLast? = some d₀
    simp
  · exact drawsOk_of_fit (headMergeShape P.lay.lk) _ ds (sumEntries_draws P.lay.lk P.work) hd'.2

/-- **The law stands, from its ninth premise on, at the rounds that the row plays.** -/
theorem headMergeInnerPlayed : HeadMergeInnerPlayed := by
  intro W₀ Rc Xi Tr X P claims weights c d₀ ds m hd
  obtain ⟨x, q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    headMergeFront W₀ Rc Xi Tr X P claims weights c d₀ ds m hd
  refine ⟨x, q2, ?_⟩
  intro work cl sv F W mask ent
  exact headMergeInner _ _ P.lay c (headMergeEntry claims weights m d₀) (m.shown.plus [⟨[], d₀⟩])
    ds
    (headMergeSaid P claims weights c m d₀ ds).tail ⟨[], d₀⟩ x work cl sv F W mask ent q1 q2 q3 q4
    q5 q6 q7 q8

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.plain_of_fit
#print axioms ProofFile.Honest.K11.merge_plain
#print axioms ProofFile.Honest.K11.sumEntries_draws
#print axioms ProofFile.Honest.K11.headMergeFront
#print axioms ProofFile.Honest.K11.headMergeInnerPlayed
