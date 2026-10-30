-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodSilent.lean: WHAT THE SILENCE OF THE MARK `goodK6Mark`
(Honest/K6/GoodMark.lean) GIVES: at challenges that fit the declared rounds of the sub-protocol "the
output head's own rounds" (K6), all three tests on its samples accept. CONDITIONAL. Lemmas with
their proofs. None of the library's goals.

  `nz_of_drawsFit`  challenges that fit the declared rounds have every word below the prime, and at
                    the four rounds in the further variable their first element is not 0
  `good_of_silent`, `good_of_silent_typed`   **where the mark is silent, at such challenges, all
                    three tests accept**; the second over a kit's messages
  `nzRounds_last`, `rounds_nz_le`   two facts on the declared rounds

What it is not. WHAT THE SILENCE DOES NOT GIVE: anything on the test `linkedK6`; anything on a state
of the verifier's. The three tests are written out: the first is the text of `drawsOk`, and the
three together that of `goodAll` (Honest/K6/GoodLaw/Tie.lean, which is not imported here). No
measure stands in this file. Called: `drawsFit_typed` (Honest/Law/Due.lean), `goodK6Nz_iff`,
`headRounds_are`, `headRounds_at2`, `headRounds_at567`, `headInFront_at`
(Honest/K6/GoodRounds.lean), `last_not_zero` (Johnson/Desc/Kinds/Law/K06FitsShape.lean),
`goodK6Mark_speaks`, `drawsOk_of_fit`, `drawFit_at` (Honest/K6/GoodMark.lean). Over files that have
not yet landed in the library: these.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.GoodMark
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.Desc.Kinds.Law.K06FitsShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E isZeroE okE)
open VerifiableInference.Desc (drawsMarkedNonzeroHaveNonzeroWords fieldPrimeWord)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Head.Par drawPoint.rounds sendThenBatch.rounds level.rounds
  sumcheck.rounds)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-- The four rounds in the further variable, in the list of rounds as data. -/
theorem nzRounds_last (p : Head.Par) : ∀ r ∈ nzRounds p,
    (headRoundsOf (headLt p) (headLPd p))[r]? = some headLastRound := by
  obtain ⟨f2, f5, f6, f7⟩ := headInFront_at p
  obtain ⟨_, y2⟩ := headRounds_at2 (headLt p) (headLPd p)
  obtain ⟨⟨_, y5⟩, ⟨_, _, y6⟩, _, _, y7⟩ := headRounds_at567 (headLt p) (headLPd p)
  intro r hr
  unfold nzRounds at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [f2, y2]
  · rw [f5, y5]
  · rw [f6, y6]
  · rw [f7, Nat.add_comm (headLPd p) (headLt p), y7]

/-- Challenges that fit the sub-protocol's declared rounds (`drawsFit p.rounds`, Honest/Frame.lean:
it rejects, too, where the list is shorter or longer than the rounds) have every word below the
prime, and at the four rounds in the further variable their first element is not 0. -/
theorem nz_of_drawsFit (p : Head.Par) (own : List Fmt.Drawn) (h : drawsFit p.rounds own = true) :
    (own.all fun d => (elemsOf d).all okE) = true ∧ goodK6Nz p own = true := by
  refine ⟨drawsOk_of_fit p.rounds own h, (goodK6Nz_iff p own).2 fun r hr => ?_⟩
  have hR := nzRounds_last p r hr
  have hd : p.rounds[r]? = some { entry := headLastRound.entry p.work } := by
    rw [headRounds_are, List.getElem?_map, hR]
    rfl
  obtain ⟨R, hR', hf⟩ := drawFit_at p.rounds own h r _ hd
  unfold drawFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hf
  have hlen : R.elems.length = headLastRound.drawn := hf.1.1.1.1.1.1.1
  have hnz := VerifiableInference.Desc.Kinds.Head.Law.last_not_zero p.work headLastRound rfl [] R
    hlen hf.1.1.2
  unfold elemOf
  rw [hR']
  show isZeroE (((elemsOf R).head?).getD OnBytes.zeroE) = false
  unfold elemsOf
  cases he : R.elems with
  | nil =>
    rw [he] at hlen
    cases hlen
  | cons x l =>
    rw [he] at hnz
    exact hnz _ List.mem_cons_self

/-- **WHERE THE MARK IS SILENT, AT SUCH CHALLENGES, ALL THREE TESTS ACCEPT.** -/
theorem good_of_silent (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn)
    (h : drawsFit p.rounds own = true) (hs : ((goodK6Mark p a).test fr own).isSome = false) :
    (own.all fun d => (elemsOf d).all okE) = true ∧ goodK6 p own = true ∧
      goodK6Nz p own = true := by
  obtain ⟨h1, h2⟩ := nz_of_drawsFit p own h
  refine ⟨h1, ?_, h2⟩
  rw [goodK6Mark_speaks] at hs
  simpa using hs

/-- No declared round of the sub-protocol samples more elements by the rule that never gives 0 than
it samples elements. -/
theorem rounds_nz_le (p : Head.Par) : ∀ z ∈ p.rounds, z.entry.drawNZ ≤ z.entry.drawE := by
  intro z hz
  rw [headRounds_are] at hz
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
  show (if r.notZero then 1 else 0) ≤ r.drawn
  unfold headRoundsOf drawPoint.rounds sendThenBatch.rounds level.rounds sumcheck.rounds at hr
  simp only [List.mem_append, List.mem_cons, List.mem_replicate, List.not_mem_nil, or_false] at hr
  casesm* _ ∨ _, _ ∧ _ <;> subst_vars <;> simp

/-- **THE SAME OVER A KIT's MESSAGES**: hC: what the kit's challenges show fits their entries, in
words below the prime (the premise of `drawsFit_typed`, Honest/Law/Due.lean). hfit: the data are the
declared rounds' own. Then at every message of the member's rounds at which the mark is silent all
three tests accept what the message shows. -/
theorem good_of_silent_typed (C : CK)
    (hC : ∀ e k (c : C.Ch e k), H2K.Fit.FitsDrawn e k (C.dr e k c) ∧
      (∀ z ∈ (C.dr e k c).elems, z.1 < fieldPrimeWord ∧ z.2.1 < fieldPrimeWord ∧ z.2.2 < fieldPrimeWord) ∧
      ((C.dr e k c).digest = none ∨ k = .sealed))
    (dsb : List RDT) (p : Head.Par) (a : Place) (hfit : List.Forall₂ KindFits dsb p.rounds)
    (fr : List Fmt.Drawn) (ρ : Iop.Rho (uLT C dsb))
    (hs : ((goodK6Mark p a).test fr (drawnT C dsb ρ)).isSome = false) :
    ((drawnT C dsb ρ).all fun d => (elemsOf d).all okE) = true ∧
      goodK6 p (drawnT C dsb ρ) = true ∧ goodK6Nz p (drawnT C dsb ρ) = true :=
  good_of_silent p a fr _ (drawsFit_typed C hC dsb p.rounds hfit (rounds_nz_le p) ρ) hs

#print axioms nzRounds_last
#print axioms nz_of_drawsFit
#print axioms good_of_silent
#print axioms rounds_nz_le
#print axioms good_of_silent_typed

end ProofFile.Honest.K6
