-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/HoldsLaws.lean: what the planner's yes on a plan says of each round; and that at the
setting "record with work" every count of an entry's plan is at most 2 ^ (work - 128).

The planner says yes of a plan (`Planned.holds`, OnBytes/Params/Planner.lean) only if every round
holds: the round's error with the distance from uniform of its draws (`wholeError`) is at most 2 ^
(work - target), an exact comparison. A round's own error is at most `wholeError` (`le_wholeError`);
so a round that holds, and every round of a plan that holds, has an error of at most 2 ^ (work -
target) (`roundHolds_sound`, `holds_rounds`). A plan that `finishHeld` returns has the setting with
which it was begun (`finish_set`, `finishHeld_set`). With OnBytes/Params/EntryCoveredRecord.lean: at
`recordLines`, and at `smallRecordLines`, for any bias (1 + x) ^ b of the record's seeds with 0 ≤ x
and 52 b x ≤ 1 (at the small lines 228 b x ≤ 1), each number of `recordCounts b x` or
`smallRecordCounts b x` is at most 2 ^ (work - 128), with the work of its round in the plan that
`entrySized` returns (`record_entry_below`, `small_record_entry_below`; `forall₂_weaken`); and the
same as shares in the extended non-negative reals: the number divided by 2 to the round's work is at
most 2 ^ -128 (`share_of_below`, `record_entry_share`, `small_record_entry_share`).

Main theorems: `le_wholeError`, `roundHolds_sound`, `holds_rounds`, `finish_set`, `finishHeld_set`,
`forall₂_weaken`, `share_of_below`, `record_entry_below`, `small_record_entry_below`,
`record_entry_share`, `small_record_entry_share`.
What is not claimed: that proof of work is worth its bits: that a round's work divides a prover's
chance is another file's matter; here the work is a number in an exponent. That a number of the two
lists bounds a prover's chance: see the head of OnBytes/Params/EntryCoveredRecord.lean. What the
planner's addition for the draws is worth: the laws drop it; no sampler's bias is compared with it.
The comparison is in OnBytes/Slice/HeldRound.lean (`held_round`): at the format's field, in a round
that draws an element and has work + 66 ≤ target, the addition pays for the sampler's bias; at a
smaller target nothing is said of such a round. That the work in a round of these two plans is the
work of the round that the dry run notes: OnBytes/Params/EntryFactsRecord.lean shows it for the 41
and 24 rounds after the first. That a number of the lists is not negative: each is, by its form; no
law. No sum over the rounds. A key's and a proof's plans. For proofs only; the program, that is the
Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.EntryCoveredRecord

set_option autoImplicit false

namespace OnBytes.Params
open Binary

/-- A round's own error is at most the error with the distance from uniform of its draws. -/
theorem le_wholeError (s : Setting) (unit : Binary) (r : PlanRound) :
    r.error.val ≤ (wholeError s unit r).val := by
  unfold wholeError
  split
  · exact le_rfl
  · have h1 : r.error.val ≤
        (r.error.add (unit.mul (.ofNat (r.entry.drawE + r.entry.drawNZ)) .up) .up).val :=
      le_trans (le_add_of_nonneg_right (val_nonneg _)) (val_add_up _ _)
    dsimp only
    split
    · exact le_trans h1 (le_trans (le_add_of_nonneg_right (val_nonneg _)) (val_add_up _ _))
    · exact h1

/-- **A round that holds has an error of at most 2 ^ (work - target).** -/
theorem roundHolds_sound {s : Setting} {unit : Binary} {r : PlanRound}
    (h : roundHolds s unit r = true) :
    r.error.val ≤ (2 : ℚ) ^ ((r.entry.work : ℤ) - (s.target : ℤ)) := by
  have h1 := le_sound _ _ h
  rw [val_twoTo] at h1
  exact (le_wholeError s unit r).trans h1

/-- **In a plan that holds every round has an error of at most 2 ^ (work - target).** -/
theorem holds_rounds {P : Planned} (h : P.holds = true) :
    ∀ r ∈ P.rounds, r.error.val ≤ (2 : ℚ) ^ ((r.entry.work : ℤ) - (P.set.target : ℤ)) := by
  unfold Planned.holds at h
  simp only [Bool.and_eq_true] at h
  have h1 := h.1.1
  unfold Planned.roundsHold at h1
  exact fun r hr => roundHolds_sound (List.all_eq_true.mp h1 r hr)

/-- A finished plan has the setting with which it was begun. -/
theorem finish_set {s : Setting} {scope : Scope} {x : Planning Unit} {P : Planned}
    (h : finish s scope x = .ok P) : P.set = s := by
  unfold finish at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      rfl

/-- So has a plan that `finishHeld` returns. -/
theorem finishHeld_set {s : Setting} {scope : Scope} {x : Planning Unit} {P : Planned}
    (h : finishHeld s scope x = .ok P) : P.set = s := by
  unfold finishHeld at h
  cases hf : finish s scope x with
  | error e =>
    rw [hf] at h
    cases h
  | ok p =>
    rw [hf] at h
    have h' : (if p.holds then (pure p : Except String Planned) else throw notAdmitted) =
        .ok P := h
    split at h'
    · cases h'
      exact finish_set hf
    · cases h'

/-- A relation that holds place by place, weakened at the members of the second list. -/
theorem forall₂_weaken {α β : Type} {R S : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b → (∀ x, ∀ y ∈ b, R x y → S x y) →
      List.Forall₂ S a b
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, w =>
    .cons (w _ _ (List.mem_cons_self ..) h)
      (forall₂_weaken t fun x y hy => w x y (List.mem_cons_of_mem _ hy))

/-- A number that is at most 2 ^ (w - 128), as a share divided by 2 ^ w: at most 2 ^ -128. -/
theorem share_of_below {c : ℝ} {w : ℕ} (h : c ≤ (2 : ℝ) ^ ((w : ℤ) - 128)) :
    ENNReal.ofReal c / 2 ^ w ≤ ((2 : ENNReal) ^ 128)⁻¹ := by
  have e : (2 : ℝ) ^ ((w : ℤ) - 128) = 2 ^ w / 2 ^ 128 := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
    norm_cast
  rw [e] at h
  have h1 : ENNReal.ofReal c ≤ (2 : ENNReal) ^ w / 2 ^ 128 := by
    refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h0 : (2 : ENNReal) ^ w ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ENNReal) ^ w ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  calc ENNReal.ofReal c / 2 ^ w ≤ (2 : ENNReal) ^ w / 2 ^ 128 / 2 ^ w :=
        ENNReal.div_le_div_right h1 _
    _ = ((2 : ENNReal) ^ 128)⁻¹ := by
        rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm ((2 : ENNReal) ^ w), mul_assoc,
          ENNReal.mul_inv_cancel h0 ht, mul_one]

/-- **At `recordLines` each count is at most 2 ^ (work - 128), with the work of its round in the
plan that `entrySized` returns**, for any bias with 0 ≤ x and 52 b x ≤ 1. -/
theorem record_entry_below {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 52 * (b : ℝ) * x ≤ 1) :
    ∃ P, entrySized recordLines =
        .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
      List.Forall₂ (fun (c : ℝ) (r : PlanRound) => c ≤ (2 : ℝ) ^ ((r.entry.work : ℤ) - 128))
        (recordCounts b x) P.rounds := by
  obtain ⟨P, hP, hc⟩ := record_entry_covered_plan hx hx1
  cases hF : finishHeld recordSet .once
      (linkPlan ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩) with
  | error e =>
    have hp := record_finish
    rw [hF] at hp
    cases hp
  | ok P' =>
    have hP' := entrySized_of record_table record_link hF
    have e : P' = P := by
      have h := hP'.symm.trans hP
      simpa using h
    subst e
    have ht : P'.set.target = 128 := by
      rw [finishHeld_set hF]
      decide
    refine ⟨P', hP, forall₂_weaken hc fun c r hr h => ?_⟩
    have h2 := holds_rounds (finishHeld_holds hF) r hr
    rw [ht] at h2
    have h3 := (Rat.cast_le (K := ℝ)).mpr h2
    rw [Rat.cast_zpow] at h3
    push_cast at h3
    exact h.trans h3

/-- **At `smallRecordLines` each count is at most 2 ^ (work - 128), with the work of its round in
the plan that `entrySized` returns**, for any bias with 0 ≤ x and 228 b x ≤ 1. -/
theorem small_record_entry_below {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 228 * (b : ℝ) * x ≤ 1) :
    ∃ P, entrySized smallRecordLines =
        .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
          smallRecordCodes, P) ∧
      List.Forall₂ (fun (c : ℝ) (r : PlanRound) => c ≤ (2 : ℝ) ^ ((r.entry.work : ℤ) - 128))
        (smallRecordCounts b x) P.rounds := by
  obtain ⟨P, hP, hc⟩ := small_record_entry_covered_plan hx hx1
  cases hF : finishHeld smallRecordSet .once
      (linkPlan ⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩) with
  | error e =>
    have hp := small_record_finish
    rw [hF] at hp
    cases hp
  | ok P' =>
    have hP' := entrySized_of small_record_table small_record_link hF
    have e : P' = P := by
      have h := hP'.symm.trans hP
      simpa using h
    subst e
    have ht : P'.set.target = 128 := by
      rw [finishHeld_set hF]
      decide
    refine ⟨P', hP, forall₂_weaken hc fun c r hr h => ?_⟩
    have h2 := holds_rounds (finishHeld_holds hF) r hr
    rw [ht] at h2
    have h3 := (Rat.cast_le (K := ℝ)).mpr h2
    rw [Rat.cast_zpow] at h3
    push_cast at h3
    exact h.trans h3

/-- **The same as shares**: each count, divided by 2 to its round's work, is at most 2 ^ -128;
for any bias with 0 ≤ x and 52 b x ≤ 1. -/
theorem record_entry_share {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 52 * (b : ℝ) * x ≤ 1) :
    ∃ P, entrySized recordLines =
        .ok (⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩, recordCodes, P) ∧
      List.Forall₂ (fun (c : ℝ) (r : PlanRound) =>
          ENNReal.ofReal c / 2 ^ r.entry.work ≤ ((2 : ENNReal) ^ 128)⁻¹)
        (recordCounts b x) P.rounds := by
  obtain ⟨P, hP, h⟩ := record_entry_below hx hx1
  exact ⟨P, hP, forall₂_weaken h fun _ _ _ hc => share_of_below hc⟩

/-- **The same as shares**: each count, divided by 2 to its round's work, is at most 2 ^ -128;
for any bias with 0 ≤ x and 228 b x ≤ 1. -/
theorem small_record_entry_share {b : ℕ} {x : ℝ} (hx : 0 ≤ x) (hx1 : 228 * (b : ℝ) * x ≤ 1) :
    ∃ P, entrySized smallRecordLines =
        .ok (⟨smallRecordLink, smallRecordTable, ⟨smallRecordG1, 97, smallRecordStages⟩⟩,
          smallRecordCodes, P) ∧
      List.Forall₂ (fun (c : ℝ) (r : PlanRound) =>
          ENNReal.ofReal c / 2 ^ r.entry.work ≤ ((2 : ENNReal) ^ 128)⁻¹)
        (smallRecordCounts b x) P.rounds := by
  obtain ⟨P, hP, h⟩ := small_record_entry_below hx hx1
  exact ⟨P, hP, forall₂_weaken h fun _ _ _ hc => share_of_below hc⟩

end OnBytes.Params

#print axioms OnBytes.Params.share_of_below
#print axioms OnBytes.Params.record_entry_share
#print axioms OnBytes.Params.small_record_entry_share
#print axioms OnBytes.Params.le_wholeError
#print axioms OnBytes.Params.roundHolds_sound
#print axioms OnBytes.Params.holds_rounds
#print axioms OnBytes.Params.finish_set
#print axioms OnBytes.Params.finishHeld_set
#print axioms OnBytes.Params.forall₂_weaken
#print axioms OnBytes.Params.record_entry_below
#print axioms OnBytes.Params.small_record_entry_below
