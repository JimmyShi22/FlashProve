--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawRoundFit.lean: THE SMALLNESS TEST, ITS FIRST HALF: WHAT THE FRAME'S TEST ON
THE ROUND ASKS AT THE KIND'S DECLARED ROUND, UNFOLDED; AND THE STEP'S YES WITH NO NAME OF A TEST
LEFT.

`step_atS_iff` (Johnson/Desc/First/K8/LawRowsStep.lean) names the frame's test `roundsFit` on its
right side. A name holds nothing: with `roundsFit` emptied the "if and only if" would stay true.
Here the test is unfolded at the kind's declared round:
  `fit_iff`: **`roundsFit [round p] [r] = true` IF AND ONLY IF r shows no item, drew no element and
    no position, drew columns x tau matrix entries, and each of these is -1, 0 or 1.**
  `step_atS_plain`: the step's yes at the carried record, both ways, with these five clauses in the
    place of the name.
  `HearStepPlain`: the same as a closed proposition, with a theorem of just that type.
Statements and proofs.
Limits. Those of LawRowsStep.lean. `Block.step` itself is the frame's text
(Johnson/Desc/Block.lean): that the fold calls it is not said here.

-/
import Johnson.Desc.First.K8.LawRowsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open OnBytes.Model

/-- **The frame's test on the round, at the kind's declared round.** -/
theorem fit_iff (p : Par) (r : Fmt.RoundView) :
    roundsFit [round p] [r] = true ↔
      r.vals = [] ∧ r.drawn.elems = [] ∧ r.drawn.poss = [] ∧
        r.drawn.trits.length = columns p * p.tau ∧ ∀ t ∈ r.drawn.trits, t = -1 ∨ t = 0 ∨ t = 1 := by
  constructor
  · intro h
    simp only [roundsFit, round, Fmt.DeclaredRound.items, Fmt.Entry.cut, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, h6⟩, _⟩, _⟩ := h
    refine ⟨?_, List.eq_nil_of_length_eq_zero h2, List.eq_nil_of_length_eq_zero h3, h4,
      fun t ht => ?_⟩
    · simpa using h1
    · rcases h6 t ht with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have ha : r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) = true := by
      rw [List.all_eq_true]
      intro t ht
      rcases h5 t ht with h | h | h <;> simp [h]
    have hz : drawsMarkedNonzeroHaveNonzeroWords (round p) r = true := by
      unfold drawsMarkedNonzeroHaveNonzeroWords
      rw [kind_rng p]
      simp [h2]
    have hz' : drawsMarkedNonzeroHaveNonzeroWords { entry := { name := "RNG", trits := columns p * p.tau } } r = true := hz
    simp [roundsFit, round, Fmt.DeclaredRound.items, Fmt.Entry.cut, h1, h2, h3, h4, ha, hz']

/-- **The step at the carried record, both ways, with no name of a test left.** -/
theorem step_atS_plain {Cl : Type} (p : Par) (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView)
    (cols : List Col) :
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols = .ok (st', n) ↔
      ∃ r, rs = [r] ∧ (r.vals = [] ∧ r.drawn.elems = [] ∧ r.drawn.poss = [] ∧
        r.drawn.trits.length = columns p * p.tau ∧ ∀ t ∈ r.drawn.trits, t = -1 ∨ t = 0 ∨ t = 1) ∧
        MeansAtS p st r st' ∧ n = 0 := by
  rw [step_atS_iff]
  constructor
  · rintro ⟨r, e, hf, hm, hn⟩
    exact ⟨r, e, (fit_iff p r).1 hf, hm, hn⟩
  · rintro ⟨r, e, hf, hm, hn⟩
    exact ⟨r, e, (fit_iff p r).2 hf, hm, hn⟩

/-- The same as a closed proposition. -/
def HearStepPlain : Prop :=
  ∀ (Cl : Type) (p : Par) (ft : Nat) (st st' : S) (n : Nat) (rs : List Fmt.RoundView) (cols : List Col),
    (approximateRangeProofDrawKind (Cl := Cl) atS p).step ft st rs cols = .ok (st', n) ↔
      ∃ r, rs = [r] ∧ (r.vals = [] ∧ r.drawn.elems = [] ∧ r.drawn.poss = [] ∧
        r.drawn.trits.length = columns p * p.tau ∧ ∀ t ∈ r.drawn.trits, t = -1 ∨ t = 0 ∨ t = 1) ∧
        MeansAtS p st r st' ∧ n = 0

theorem hearStepPlain : HearStepPlain :=
  fun _ p ft st st' n rs cols => step_atS_plain p ft st st' n rs cols

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.fit_iff
#print axioms VerifiableInference.Desc.First.K8.step_atS_plain
#print axioms VerifiableInference.Desc.First.K8.hearStepPlain
