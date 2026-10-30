-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/LawRounds.lean: THE SMALLNESS TEST, ITS FIRST HALF: ITS ROUND HAS THE PROVED
BLOCK'S SHAPE, AND, WITH ONE INSTANCE, THE BLOCK'S ERROR AT THAT ROUND IS AT MOST THE BOUND THAT THE
PLANNER'S ROUTINE BOOKS FOR THE ROUND'S ENTRY.

Nothing is counted anew: the library's `call_rng_block` (OnBytes/Tie/Pv/Tail/CallRng.lean) says it
of the planner's routine planRng and the block of Cb/Pv/Tail/Block.lean. Here the kind's DECLARED
round (Johnson/Desc/First/K8/Hear.lean) is shown to have the very entry that planRng adds to the
plan, at the place's numbers, and the library's theorem is carried to it.
  `entry_eq`: the entry that planRng adds at the place's number of columns is the kind's declared
    entry, if the place's number of combinations is the one that follows from the setting, and the
    setting asks no work of this round.
  `rounds_law`: from an idle state of the planner, if planRng ends well at the place's columns: one
    round is added; its entry is the kind's; the proved block's rounds have the shape of that entry;
    with one instance the block's error, as a part of all values that can be drawn, is at most the
    bound that the planner books for the round.
  `setting_of_entry`, `rounds_law_of_entry`: the two premises on the setting follow from ONE
    equation: the entry that planRng adds is the kind's declared entry (and there is a column).
Statements and proofs. Limits: THAT EQUATION IS PAID NOWHERE HERE: that the made plan's round at
this place is the one that planRng adds under the setting of the file's parameter lines, and that
this setting has one instance, is owed. The kind declares its round with no work: at a setting that
asks work of this round the entries differ, the test on the plan says no, and the description
refuses every proof. Further: those of CallRng.lean: nothing here says that the block is sound at
this error (that is `block_good`, Law.lean); the shape is the one before proof of work is added; the
two premises on the setting are the caller's to bring (in a file's description the test on the plan
holds the declared entries against the made plan's: FileDescription.planOk).

-/
import Johnson.Desc.First.K8.Law
import OnBytes.Tie.Pv.Tail.CallRng

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop OnBytes OnBytes.Model OnBytes.Params OnBytes.G4 Cb.Pv.Tail OnBytes.Tie.Pv.Tail

/-- The entry that the planner's routine adds is the kind's declared entry. -/
theorem entry_eq (p : Par) (st : Setting) (ht : p.tau = rngCombinations st .request)
    (hw : st.workOf .small .request = 0) :
    (rngRound st (rngSize st (columns p))).entry = (round p).entry := by
  simp [rngRound, rngSize, round, hw, ht]

/-- And back: if the entry that the planner's routine adds at the place's number of columns IS the
kind's declared entry, and there is a column, then the two premises on the setting hold. In a file's
description the test on the plan holds the declared rounds against the made plan's, whole
(`FileDescription.planOk`): so where the plan's round at this place is the one that planRng adds under st,
that equation is what the test gives. -/
theorem setting_of_entry (p : Par) (st : Setting) (hc : columns p ≠ 0)
    (he : (rngRound st (rngSize st (columns p))).entry = (round p).entry) :
    p.tau = rngCombinations st .request ∧ st.workOf .small .request = 0 := by
  have h1 : (rngRound st (rngSize st (columns p))).entry.trits = (round p).entry.trits := by rw [he]
  have h2 : (rngRound st (rngSize st (columns p))).entry.work = (round p).entry.work := by rw [he]
  have h1' : columns p * rngCombinations st .request = columns p * p.tau := h1
  exact ⟨(Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc) h1').symm, h2⟩

/-- **The kind's round has the proved block's shape, and with one instance the block's error is at
most the bound that the planner's routine books.** -/
theorem rounds_law {K : Type} {p : Par} {s : Size} (hf : Fits p s) (Λ : Letters K s) (st : Setting)
    (ht : p.tau = rngCombinations st .request) (hw : st.workOf .small .request = 0) (pl q :
        PlanState)
    (hp : Idle st pl) (h : planRng (columns p) pl = .ok ((), q)) :
    Idle st q ∧ q.rounds = pl.rounds.push (rngRound st (rngSize st (columns p))) ∧
      (rngRound st (rngSize st (columns p))).entry = (round p).entry ∧
      ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(round p).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
          [planVal (rngRound st (rngSize st (columns p))).error]) := by
  obtain ⟨a, r, sh, er⟩ := call_rng_block Λ st (columns p) (columns_eq hf) (hf.tau.trans ht) pl q hp
      h
  rw [entry_eq p st ht hw] at sh
  exact ⟨a, r, entry_eq p st ht hw, sh, er⟩

/-- The same from the one equation of entries. -/
theorem rounds_law_of_entry {K : Type} {p : Par} {s : Size} (hf : Fits p s) (Λ : Letters K s) (st :
    Setting)
    (hc : columns p ≠ 0) (he : (rngRound st (rngSize st (columns p))).entry = (round p).entry) (pl q
        : PlanState)
    (hp : Idle st pl) (h : planRng (columns p) pl = .ok ((), q)) :
    ShapeIsAll Cb.Gl.E Cb.Gl.F (R Λ).shape [(round p).entry] ∧
      (st.instances ≤ 1 →
        List.Forall₂ (· ≤ ·)
          (List.zipWith (fun e n : ℕ => (e : ℚ) / (n : ℚ)) (eps Λ).toList (R Λ).shape.chalList)
          [planVal (rngRound st (rngSize st (columns p))).error]) :=
  (rounds_law hf Λ st (setting_of_entry p st hc he).1 (setting_of_entry p st hc he).2 pl q hp
      h).2.2.2

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.setting_of_entry
#print axioms VerifiableInference.Desc.First.K8.rounds_law_of_entry
#print axioms VerifiableInference.Desc.First.K8.entry_eq
#print axioms VerifiableInference.Desc.First.K8.rounds_law
