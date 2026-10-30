-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/AttGStays.lean: WHAT THE LOOKUP ON THE CALLS RETURNED STAYS
FROM AN ATTENTION SEGMENT's OWN ROUNDS ON. At an attention segment the field g of the open
segment's own part is laid by the lookup on the calls. Five members stand between the border behind
it and the batching: the segment's own rounds (K5) · the reads' sending (K1) · the smallness test's
draw (K8) · the digits' sending (K1) · the lookup on the digits (K3). Each of these kinds has its
clause of the letter `keeps`; none turns g: here the first four,
clause by clause, as lemmas; the fifth stands in Honest/Thread/K3Stays.lean, so that this file does
not stand over that kind's many files. With `staysBy_att_read` (Honest/Thread/RidersAtt.lean) a
clause `riderAtt lo hi (fun a => R a.g)` stays past each. No definition. Six conditional lemmas.

  `attG_k5`, `attG_commit`, `attG_quiet`, `attG_reads`, `attG_k8`   clause by clause
  `staysBy_attG`   the staying, general in the thread and in R

Limits. That the thread's `keeps` at these members gives these clauses is the premise hk of
`staysBy_attG`: it is shown here at no thread. IT IS NOT HAD BY THE MEMBER's KIND ALONE: a kind's
clause by the place may give the sort's own clause only under public facts on that place: so at the
lookup on the digits (Honest/Thread/K3Stays.lean's head says which). Who lays the clause and what R
is, is not said here. It stands over
files of other houses which are not sealed: how many, and whose, its cover says by a count on the
machine that compiled it. None is one of the library's goals. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersAtt
import Johnson.Desc.K5.Honest.Law.KeepsM
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsReads
import Johnson.Desc.K8.Honest.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S AttOwn)

/-- The segment's own rounds. -/
theorem attG_k5 {x : OnBytes.Params.AttentionRounds} {s s' : S}
    (h : H2K5.Honest.K5KeepsM x s s') :
    ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨-, a₀, hd, G, rs, ha₀, -, rfl⟩ := h
  intro a ha
  rw [ha₀] at ha
  cases ha
  exact ⟨{ a₀ with F := G, heard5 := some hd }, rfl, rfl⟩

/-- A segment's later commitment. -/
theorem attG_commit {s s' : S} (h : ProofFile.Honest.K1.K1CommitKeeps s s') :
    ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨-, -, -, L, F, tl, L', F', -, -, -, hh, -, -⟩ := h
  intro a ha
  refine ⟨{ a with L := L', F := F' }, ?_, rfl⟩
  rw [hh]
  simp [S.putLink, S.putFork, ha]

/-- The step without a round behind the reads' commitment. -/
theorem attG_quiet {s s' : S} (h : ProofFile.Honest.K1.K1QuietKeeps s s') :
    ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨-, -, -, -, -, -, -, -, hh⟩ := h
  intro a ha
  rcases hh with ⟨a₁, tl, h1, -⟩ | ⟨a₁, t, tl, h1, h2⟩ | ⟨a₁, t, tl, h1, -, -⟩
  · rw [ha] at h1
    cases h1
  · rw [ha] at h1
    cases h1
    exact ⟨_, h2, rfl⟩
  · rw [ha] at h1
    cases h1

/-- The whole member at a segment's reads. -/
theorem attG_reads {s s' : S} (h : ProofFile.Honest.K1.K1ReadsKeeps s s') :
    ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨m, h1, h2⟩ := h
  intro a ha
  obtain ⟨a₁, e1, g1⟩ := attG_commit h1 a ha
  obtain ⟨a₂, e2, g2⟩ := attG_quiet h2 a₁ e1
  exact ⟨a₂, e2, g2.trans g1⟩

/-- The smallness test's draw. -/
theorem attG_k8 {s s' : S} (h : VerifiableInference.Desc.First.K8.Honest.K8Keeps s s') :
    ∀ a, s.here = .att a → ∃ a', s'.here = .att a' ∧ a'.g = a.g := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  intro a ha
  refine ⟨{ a with tl := { tl with cfF := cf, cfFirst := first } }, ?_, rfl⟩
  simp [S.putTl, ha]

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE STAYING**, general in the thread and in the sentence R on g. -/
theorem staysBy_attG {b lo hi : Nat} {R : Option OnBytes.Model.Forest.Heard → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .att a →
      ∃ a', s'.here = .att a' ∧ a'.g = a.g) : StaysBy T b (riderAtt lo hi fun a => R a.g) :=
  staysBy_att_read T (fun a => a.g) hk

end ProofFile.Honest

#print axioms ProofFile.Honest.attG_k5
#print axioms ProofFile.Honest.attG_commit
#print axioms ProofFile.Honest.attG_quiet
#print axioms ProofFile.Honest.attG_reads
#print axioms ProofFile.Honest.attG_k8
#print axioms ProofFile.Honest.staysBy_attG
