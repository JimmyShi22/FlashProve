-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RoundsNot.lean: the form "every written round is below, with the radii pinned"
(`RoundsHoldAt`, RoundsHold.lean) fails, as a proposition, where the first stage's radius is not
inside the Johnson bound.

Why. RoundsHoldPlaces.lean shows at eight places that tests with code say no at the distances for
radii, while the bare comparison on "BAT"'s count says yes there. These are lines on tests beside
the form. Here the proposition itself is refuted, at every place and every bound εs. Of the other
form `RoundsBelowAt`, which has no clause on the radii, nothing of the kind is shown, and by other
files' programs its comparisons pass at such radii.
Main names:
  `listMax_zero`, `lstJ_zero`: where the Johnson bound's comparison fails, the bound on the list is
    0 (its divisor is cut off to 0).
  `not_listAt_zero`: no code has lists of at most 0: an encoding is within any radius of itself.
  `not_roundsHoldAt_joh`: no place has `RoundsHoldAt p rad εs` if `rad` at the first stage fails
    `InJohnson` at the stage's number of positions and its distance.
  `not_roundsHoldAt_inJB`: the same from the test with code: `inJB` (Johnson/Top/H/StageJ.lean) says
    no.
  `not_roundsHoldAt`, `not_roundsHoldAt_d`: where the first radius is at least the distance; so at
    `rad := fun s => s.d`.
How: the form's clause on the first stage's list would be `ListAt e 0`; and, for the last two, a
place whose declared rounds can be written has two stages at least, and `CodesAt` then asks that the
first stage's radius is below its distance.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: of the first stage's radius alone: nothing on a later stage's. From below nothing is refuted
here: at a small radius the facts on codes hold, and only the comparisons can refuse
(RoundsHoldPlaces.lean has tests that say no at the radius 0). Nothing on soundness. Nothing on
hiding.

-/
import Johnson.Desc.K12.Law.RoundsHold

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Top.H (inJB)
open scoped ENNReal

/-- Where the comparison fails, the divisor is cut off to 0. -/
theorem listMax_zero {n d e : ℕ} (h : ¬ Cb.InJohnson n d e) : Cb.listMax n d e = 0 := by
  unfold Cb.listMax
  rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_lt h), Nat.div_zero]

theorem lstJ_zero {s : Sg} {e : ℕ} (h : ¬ Cb.InJohnson (2 ^ s.C.a) s.d e) : s.lstJ e = 0 :=
  listMax_zero h

/-- No code has lists of at most 0. -/
theorem not_listAt_zero {s : Sg} (e : ℕ) : ¬ s.cIn.ListAt e 0 := by
  intro h
  have h0 := h (s.cIn.enc 0 0)
  have hp : 0 < Prob.cnt fun w : (s.cIn.J → _) × (s.cIn.Q → _) =>
      s.cIn.Near e (s.cIn.enc 0 0) (s.cIn.enc w.1 w.2) := by
    unfold Prob.cnt
    haveI : Nonempty {w : (s.cIn.J → _) × (s.cIn.Q → _) //
        s.cIn.Near e (s.cIn.enc 0 0) (s.cIn.enc w.1 w.2)} := ⟨⟨(0, 0), by
      show Prob.cnt _ ≤ e
      have : (Prob.cnt fun x => s.cIn.T (s.cIn.enc 0 0) x ≠ s.cIn.T (s.cIn.enc 0 0) x) = 0 := by
        unfold Prob.cnt
        haveI : IsEmpty {x // s.cIn.T (s.cIn.enc 0 0) x ≠ s.cIn.T (s.cIn.enc 0 0) x} :=
          ⟨fun x => x.2 rfl⟩
        exact Nat.card_of_isEmpty
      rw [this]
      exact Nat.zero_le _⟩⟩
    exact Nat.card_pos
  exact absurd h0 (Nat.not_le.2 hp)

/-- **No place has the form at a first radius that is not inside the Johnson bound.** -/
theorem not_roundsHoldAt_joh (p : P12) (rad : Sg → ℕ) (εs : ℝ≥0∞)
    (hr : ∀ a rest, p.nums.stages = a :: rest →
      ¬ Cb.InJohnson (2 ^ (sgOf a).C.a) (sgOf a).d (rad (sgOf a))) :
    ¬ RoundsHoldAt p rad εs := by
  rintro ⟨a, rest, w0, l, c, e1, _, _, _, _, _, _, _, _, hL⟩
  rw [lstJ_zero (hr a rest e1)] at hL
  exact not_listAt_zero _ hL

/-- **No place has the form at a first radius that is not below the distance.** -/
theorem not_roundsHoldAt (p : P12) (rad : Sg → ℕ) (εs : ℝ≥0∞)
    (hr : ∀ a rest, p.nums.stages = a :: rest → (sgOf a).d ≤ rad (sgOf a)) :
    ¬ RoundsHoldAt p rad εs := by
  rintro ⟨a, rest, w0, l, c, e1, e2, _, _, _, _, _, _, hC, _⟩
  cases rest with
  | nil =>
    unfold writtenOf H2U.roundsOfNums at e2
    rw [e1] at e2
    cases e2
  | cons b rest =>
    rw [e1] at hC
    exact absurd hC.1 (Nat.not_lt.2 (hr a _ e1))

theorem not_roundsHoldAt_d (p : P12) (εs : ℝ≥0∞) : ¬ RoundsHoldAt p (fun s => s.d) εs :=
  not_roundsHoldAt p _ εs fun _ _ _ => Nat.le_refl _

/-- The same from the test with code on the first stage's radius. -/
theorem not_roundsHoldAt_inJB (p : P12) (rad : Sg → ℕ) (εs : ℝ≥0∞)
    (hr : ∀ a rest, p.nums.stages = a :: rest → inJB (sgOf a) (rad (sgOf a)) = false) :
    ¬ RoundsHoldAt p rad εs := by
  intro h
  obtain ⟨a, rest, _, _, _, e1, _⟩ := id h
  have hb := hr a rest e1
  by_cases hd : rad (sgOf a) < (sgOf a).d
  · refine not_roundsHoldAt_joh p rad εs (fun a' rest' e' => ?_) h
    obtain ⟨rfl, _⟩ := List.cons.inj (e'.symm.trans e1)
    intro hJ
    have : inJB (sgOf a') (rad (sgOf a')) = true := by
      simp only [inJB, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hd, hJ⟩
    rw [hb] at this
    cases this
  · refine not_roundsHoldAt p rad εs (fun a' rest' e' => ?_) h
    obtain ⟨rfl, _⟩ := List.cons.inj (e'.symm.trans e1)
    exact Nat.le_of_not_lt hd

end H2K.Pub

#print axioms H2K.Pub.not_listAt_zero
#print axioms H2K.Pub.not_roundsHoldAt_joh
#print axioms H2K.Pub.not_roundsHoldAt
#print axioms H2K.Pub.not_roundsHoldAt_d
#print axioms H2K.Pub.not_roundsHoldAt_inJB
