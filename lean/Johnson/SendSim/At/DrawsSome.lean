-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/DrawsSome.lean: the two rounds of a sub-protocol of the kind K1 can sample some
list of challenges, at all public numbers.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has.
  draws_some   For all public numbers P there is a list of challenges ds with
               drawsFit (K1.rounds P) ds = true.
  someDraws    The list that the proof takes: in the first round every sampled element is 1; the
               second round samples nothing.

How it fits. The fields exact and fresh speak only of lists of challenges that the member's rounds
can sample (drawsFit, Johnson/Desc/ProofFile/Honest/Frame.lean). If no list could be sampled, both
would hold vacuously. This lemma shows that the premise can be met wherever the member's rounds are
K1.rounds P; draws_send (SeatedAt.lean beside this file) says what such a list holds. A lemma on
lists: no distribution is named. Not one of the release's goal statements.

Limits. One list, at the kind's own two rounds. That a member of a description has just these rounds
is not stated here (for K1's own lot: member_of_own, Johnson/SendSim/Seat/AtDesc.lean). The other
premises inside exact and fresh (the bound on queried positions; for exact, a front that has the
state's rounds and a column for every read) are not met here by a theorem.
-/
import Johnson.SendSim.At.SeatedAt

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

/-- A list of challenges for the kind's two rounds: every sampled element is 1. -/
def someDraws (P : K1.Par) : List Fmt.Drawn :=
  [⟨List.replicate (P.seeds * (P.coordinates + 1)) (1, 0, 0), [], [], none⟩, ⟨[], [], [], none⟩]

/-- **The kind's two rounds can sample some list of challenges.** -/
theorem draws_some (P : K1.Par) : ∃ ds, drawsFit (K1.rounds P) ds = true := by
  refine ⟨someDraws P, ?_⟩
  have hk : Fmt.kindOf (K1.seedEntry P).name = some .seeds := by
    show Fmt.kindOf "SEND seed" = some .seeds
    decide
  have h1 : drawFit { entry := K1.seedEntry P }
      ⟨List.replicate (P.seeds * (P.coordinates + 1)) (1, 0, 0), [], [], none⟩ = true := by
    simp only [drawFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨?_, rfl⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · exact List.length_replicate
    · intro x hx
      cases hx
    · intro x hx
      cases hx
    · unfold drawsMarkedNonzeroHaveNonzeroWords
      rw [hk]
      simp only [Option.any_some, List.all_eq_true, Bool.or_eq_true]
      intro x hx
      right
      rw [List.eq_of_mem_replicate (List.of_mem_zip hx).2]
      decide
    · intro x hx
      rw [List.eq_of_mem_replicate hx]
      decide
  have h2 : drawFit { entry := K1.answerEntry P } ⟨[], [], [], none⟩ = true := by
    obtain ⟨k, hk2⟩ : ∃ k, Fmt.kindOf (K1.answerEntry P).name = some k := by
      show ∃ k, Fmt.kindOf "SEND answer" = some k
      exact Option.isSome_iff_exists.1 (by decide)
    simp only [drawFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, rfl⟩
    · intro x hx
      cases hx
    · intro x hx
      cases hx
    · unfold drawsMarkedNonzeroHaveNonzeroWords
      rw [hk2]
      simp only [Option.any_some, List.zip_nil_right, List.all_nil]
    · intro x hx
      cases hx
  show (drawFit { entry := K1.seedEntry P } _ &&
    (drawFit { entry := K1.answerEntry P } _ && true)) = true
  rw [h1, h2]
  rfl

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.draws_some
