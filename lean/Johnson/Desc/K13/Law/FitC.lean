-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FitC.lean: what `Psc.run` hands on at the batching's claim and summand, field
by field. Lemmas with their proofs.
Main names:
  `of_fits`: what the test on the pile's form gives.
  `run_fields`: where the run returns: the sizes that it has tested, and each field that the row
    handed on is made of.
Used of `verify-on-bytes`, pure functions: `Batt.fits`, `Batt.claimOf`, `Batt.summandOf`,
`Psc.run`, `Psc.varsOf`, `Psc.masksOf`, `Psc.hidingWalk`, `Psc.claimAfter`, `zipT`.

What is not claimed. Nothing where the run returns nothing. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.FitB
import OnBytes.Tie.Pv.Psc.Run.PscPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.L5.Layers (rd sRounds)

/-- What the test on the pile's form gives. -/
theorem of_fits {k : ℕ} {pile : List TensorRow} (x : E) (h : Batt.fits k pile = true) :
    (Batt.claimOf pile x).vars = wsOf k ∧ 1 ≤ k ∧ ∀ r ∈ pile, r.psi.length = k := by
  cases pile with
  | nil => simp [Batt.fits] at h
  | cons r l =>
    simp only [Batt.fits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, h1, fun s hs => (h2 s hs).1.1⟩
    show List.replicate (((r :: l).head?.map (·.psi.length)).getD 0) (Psc.Weight.plain 3) = _
    simp [(h2 r List.mem_cons_self).1.1]

/-- A member of a list stands beside the repeated value. -/
theorem mem_zip_replicate {α β : Type} (a : α) : ∀ (k : ℕ) (l : List β), l.length = k →
    ∀ b ∈ l, (a, b) ∈ (List.replicate k a).zip l
  | 0, [], _, _, hb => by cases hb
  | k + 1, c :: l, hl, b, hb => by
    rw [List.replicate_succ, List.zip_cons_cons]
    rcases List.mem_cons.1 hb with rfl | hb
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_zip_replicate a k l (by simpa using hl) b hb)
  | 0, _ :: _, hl, _, _ => by simp at hl
  | _ + 1, [], hl, _, _ => by simp at hl

/-- The walk of the hiding polynomial at the rounds' challenges. -/
abbrev walkOf (k : ℕ) (h : Psc.Heard) : List E × E :=
  Psc.hidingWalk ((wsOf k).zip (h.rounds.map (·.2)))

/-- What the run hands on, field by field, and the sizes that it has tested. -/
theorem run_fields {k : ℕ} {pile : List TensorRow} {x : E} {fresh : List Slot} {h : Psc.Heard}
    {o : Psc.Out} (hf : Batt.fits k pile = true)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o) :
    h.rounds.length = k ∧ (∀ p ∈ h.rounds, p.1.length = 2) ∧ fresh.length = 1 + 2 * k ∧
    o.point = h.rounds.map (·.2) ∧
    o.rowMasks = fresh.zip (walkOf k h).1 ++
      Psc.scaleForm (mulE h.eps (walkOf k h).2) (Batt.claimOf pile x).masks ∧
    o.rowMaps = ((Psc.powers oneE x pile.length).zip pile).map (fun p =>
      mulE h.eps (mulE p.1 (eqEval p.2.psi (h.rounds.map (·.2))))) ∧
    o.rowTarget = subE (Psc.claimAfter (wsOf k) h.rounds
      (addE h.mu (mulE h.eps (Batt.claimOf pile x).target))) (mulE h.eps zeroE) := by
  obtain ⟨hcv, hk, -⟩ := of_fits x hf
  have hv : Psc.varsOf (Batt.claimOf pile x) (Batt.summandOf pile x) = wsOf k := by
    rw [← hcv]
    rfl
  have hm : Psc.masksOf (Batt.claimOf pile x) (Batt.summandOf pile x) = 1 + 2 * k := by
    unfold Psc.masksOf
    rw [hv]
    simp [Psc.hidingEntries, Batt.summandOf, Psc.Weight.plain]
    omega
  unfold Psc.run at hr
  simp only [hv, hm, hcv] at hr
  split at hr
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.length_replicate] at hc
    obtain ⟨⟨⟨⟨⟨_, h1⟩, h2⟩, _⟩, _⟩, h6⟩ := hc
    have ho := Option.some.inj hr
    have ht : (h.rounds.map (·.2)).take k = h.rounds.map (·.2) :=
      List.take_of_length_le (by simp [h2])
    refine ⟨h2, fun p hp => ?_, h1, ?_, ?_, ?_, ?_⟩
    · have := h6 _ (mem_zip_replicate (Psc.Weight.plain 3) k h.rounds h2 p hp)
      have e : (Psc.Weight.plain 3).d = 3 := rfl
      simp only [e] at this
      omega
    · rw [← ho]
      simpa using ht
    · rw [← ho]
    · rw [← ho]
      simp [Batt.summandOf, Batt.chiOf, zipT_eq, ht]
    · rw [← ho]
      simp [Batt.summandOf]
  · cases hr

end VerifiableInference.Desc.K13.Law
