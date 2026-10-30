-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/PartLaw.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: two
small lemmas that tie the part's second stop (Honest/K8/Part.lean: `smallHid`) and the frame's test
on a challenge (Honest/Frame.lean: `drawFit`) to the program `leaves` and to the library's typed
matrix (Johnson/Desc/K8/Honest/WindowLaw.lean). Statements and proofs. Lemmas; none of the
library's goals.

  `smallHid_isSome`   the stop speaks just if the part has heard its round's challenge and
                       `leaves` finds a combination outside its window in that challenge's sequence
  `smallHid_none`     where the stop is silent behind the round, `leaves` finds nothing: what
                       whoever sends the array of digits holds in hand
  `drawFit_listOf`    a challenge that the kind's round can draw holds the sequence of some typed
                       matrix
Limits. No measure is given here on the frame's lists of challenges. That the sub-protocol which a
description seats at the kind's place has just the kind's one declared round is not said here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Part
import Johnson.Desc.K8.Honest.WindowLawProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open VerifiableInference.Desc.First.K8 (Par Fits columns_eq)
open VerifiableInference.Desc.First.K8.Honest (leaves listOf_onto)

/-- The stop speaks just if the part has heard its round's challenge and the program finds a
combination outside its window in that challenge's sequence. -/
theorem smallHid_isSome (p : Par) (v : SmallAsk) (front own : List Fmt.Drawn) :
    (smallHid p v front own).isSome = true ↔
      ∃ d, own.head? = some d ∧ (leaves p v.cell d.trits.toArray).isSome = true := by
  unfold smallHid
  cases own.head? with
  | none => simp
  | some d => simp

/-- Where the stop is silent behind the round, the program finds nothing. -/
theorem smallHid_none (p : Par) (v : SmallAsk) (front : List Fmt.Drawn) (d : Fmt.Drawn)
    (h : smallHid p v front [d] = none) : leaves p v.cell d.trits.toArray = none := by
  cases hl : leaves p v.cell d.trits.toArray with
  | none => rfl
  | some x =>
    have h1 := (smallHid_isSome p v front [d]).2 ⟨d, rfl, by rw [hl]; rfl⟩
    rw [h] at h1
    exact Bool.noConfusion h1

/-- A challenge that the kind's round can draw holds the sequence of some typed matrix. -/
theorem drawFit_listOf (p : Par) (s : Size) (h : Fits p s) (R : Fmt.Drawn)
    (hR : drawFit (VerifiableInference.Desc.First.K8.round p) R = true) :
    ∃ β : Dr s, R.trits.toArray = listOf β := by
  unfold drawFit at hR
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hR
  refine listOf_onto s R.trits ?_ fun t ht => ?_
  · rw [columns_eq h, h.tau]
    exact hR.1.1.1.1.1.2
  · rcases hR.1.1.1.2 t ht with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.smallHid_isSome
#print axioms ProofFile.Honest.K8.smallHid_none
#print axioms ProofFile.Honest.K8.drawFit_listOf
