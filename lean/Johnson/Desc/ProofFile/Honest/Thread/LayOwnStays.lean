-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/LayOwnStays.lean: WHAT A LAYERS' SEGMENT's OWN ROUNDS RETURNED
STAYS ON TOWARD ITS BATCHING; AND THE SMALLNESS TEST's RECORD STAYS PAST THE HEAD's DIGITS' SENDING.
As Honest/Thread/AttGStays.lean at an attention segment: four members stand between the border
behind a layers' segment's own rounds (K4) and the batching: the reads' sending (K1) · the smallness
test's draw (K8) · the digits' sending (K1) · the lookup on the digits (K3). Each of these kinds'
lemmas gives its clause of the letter `keeps`; none turns the field own of the open part: here the
first three, clause by clause, as lemmas; the fourth stands in Honest/Thread/K3Stays.lean. Beside
them: a later commitment (K1) leaves the field tl of the head's own part: for the rider of span one
on the count of folds drawn. No definition. Six conditional lemmas.

  `layOwn_commit`, `layOwn_quiet`, `layOwn_reads`, `layOwn_k8`   clause by clause
  `staysBy_layOwn`   the staying, general in the thread and in the sentence on own
  `headTl_commit`    a later commitment leaves the head's part's tl

Limits. That the thread's `keeps` at these members gives these clauses is the premise hk of
`staysBy_layOwn`: it is shown here at no thread. IT IS NOT HAD BY THE MEMBER's KIND ALONE: a kind's
clause by the place may give the sort's own clause only under public facts on that place: so at the
lookup on the digits (Honest/Thread/K3Stays.lean's head says which). The batching's own member is
not served here (a corollary of its kind's authors has it). It stands over files of other authors
which are not sealed: how many, and whose, its cover says by a count on the machine that compiled
it. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RidersLay
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsReads
import Johnson.Desc.K8.Honest.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S LayOwn)

/-- A segment's later commitment. -/
theorem layOwn_commit {s s' : S} (h : ProofFile.Honest.K1.K1CommitKeeps s s') :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  obtain ⟨-, -, -, L, F, tl, L', F', -, -, -, hh, -, -⟩ := h
  intro a ha
  refine ⟨{ a with L := L', F := F' }, ?_, rfl⟩
  rw [hh]
  simp [S.putLink, S.putFork, ha]

/-- The step without a round behind the reads' commitment. -/
theorem layOwn_quiet {s s' : S} (h : ProofFile.Honest.K1.K1QuietKeeps s s') :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  obtain ⟨-, -, -, -, -, -, -, -, hh⟩ := h
  intro a ha
  rcases hh with ⟨a₁, tl, h1, h2⟩ | ⟨a₁, t, tl, h1, -⟩ | ⟨a₁, t, tl, h1, -, -⟩
  · rw [ha] at h1
    cases h1
    exact ⟨_, h2, rfl⟩
  · rw [ha] at h1
    cases h1
  · rw [ha] at h1
    cases h1

/-- The whole member at a segment's reads. -/
theorem layOwn_reads {s s' : S} (h : ProofFile.Honest.K1.K1ReadsKeeps s s') :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  obtain ⟨m, h1, h2⟩ := h
  intro a ha
  obtain ⟨a₁, e1, g1⟩ := layOwn_commit h1 a ha
  obtain ⟨a₂, e2, g2⟩ := layOwn_quiet h2 a₁ e1
  exact ⟨a₂, e2, g2.trans g1⟩

/-- The smallness test's draw. -/
theorem layOwn_k8 {s s' : S} (h : VerifiableInference.Desc.First.K8.Honest.K8Keeps s s') :
    ∀ a, s.here = .lay a → ∃ a', s'.here = .lay a' ∧ a'.own = a.own := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  intro a ha
  refine ⟨{ a with tl := { tl with cfF := cf, cfFirst := first } }, ?_, rfl⟩
  simp [S.putTl, ha]

/-- A later commitment leaves the smallness test's record of the head's own part. -/
theorem headTl_commit {s s' : S} (h : ProofFile.Honest.K1.K1CommitKeeps s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.tl = a.tl := by
  obtain ⟨-, -, -, L, F, tl, L', F', -, -, -, hh, -, -⟩ := h
  intro a ha
  by_cases ho : a.opened = true
  · refine ⟨{ a with L := L', F := F' }, ?_, rfl⟩
    rw [hh]
    simp [S.putLink, S.putFork, ha, ho]
  · refine ⟨a, ?_, rfl⟩
    rw [hh]
    simp [S.putLink, S.putFork, ha, ho]

variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-- **THE STAYING**, general in the thread and in the sentence R on own. -/
theorem staysBy_layOwn {b lo hi : Nat} {R : Option OnBytes.Model.Layer.Own → Prop}
    (hk : ∀ s s', T.keeps b s s' → ∀ a, s.here = .lay a →
      ∃ a', s'.here = .lay a' ∧ a'.own = a.own) : StaysBy T b (riderLay lo hi fun a => R a.own) :=
  staysBy_lay_read T (fun a => a.own) hk

end ProofFile.Honest

#print axioms ProofFile.Honest.layOwn_commit
#print axioms ProofFile.Honest.layOwn_quiet
#print axioms ProofFile.Honest.layOwn_reads
#print axioms ProofFile.Honest.layOwn_k8
#print axioms ProofFile.Honest.headTl_commit
#print axioms ProofFile.Honest.staysBy_layOwn
