-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/PortKit.lean: how a round of a reduction is compared with a round
that the planner adds.

A reduction of the proof library has, round by round, a number n of values of the verifier's message
and a count c of bad values among them. The planner (OnBytes/Params/Planner.lean) describes a round
by its draws, the bytes sent before it and a bound (`RoundSpec`, OnBytes/Params/PlanningLaws.lean).
Definitions and small lemmas, with their proofs. No block occurs here.
Main names:
  `valuesOf q y`: the number of values of the verifier's message of the planned round y, at a field
    of q elements: q for each drawn element, q - 1 for each that is not 0; 1 for any other round.
  `bytesOf y`: the bytes that the prover sends before the round's message.
  `Fits q cn y`: a round with cn.1 bad values of cn.2 fits y: the message of y has cn.2 values, and
    the bound of y is `Bound.ratio a b` for numbers a, b with 0 < b and cn.1 * b = a * cn.2; a round
    without a verifier's message has no bad value.
  `Covered s c cn y`: cn.1 / cn.2 is at most the error that a plan holds for y.
  `round_once`: what a plan holds of a round under the scope `.once`.
  `fits_covered`: a round that fits is covered under the scope `.once`, if its bound is not marked
    bad.
Limits: nothing on whether a count bounds a prover's chance. `Fits` names the term of a bound, not
its value. The scope `.request` with several instances is not treated. For proofs only.

-/
import OnBytes.Params.MorePrices
import OnBytes.Params.PlanningLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv
open OnBytes OnBytes.Params

/-- The number of values of the verifier's message of a planned round, at q elements. -/
def valuesOf (q : ℕ) : RoundSpec → ℕ
  | .said _ _ _ d _ _ _ => (q - 1) ^ d.drawNZ * q ^ (d.drawE - d.drawNZ)
  | _ => 1

/-- The bytes that the prover sends before the round's message. -/
def bytesOf : RoundSpec → ℕ
  | .said _ _ _ _ b _ _ => b
  | .silent _ b _ => b
  | .record _ _ _ => 0

/-- A round with cn.1 bad values of cn.2 fits the planned round y. -/
def Fits (q : ℕ) (cn : ℕ × ℕ) (y : RoundSpec) : Prop :=
  valuesOf q y = cn.2 ∧
    match y with
    | .said _ _ e _ _ _ _ => ∃ a b, 0 < b ∧ e = Bound.ratio a b ∧ cn.1 * b = a * cn.2
    | _ => cn.1 = 0

/-- The share of the bad values is at most the error that a plan holds for y. -/
def Covered (s : Setting) (c : Scope) (cn : ℕ × ℕ) (y : RoundSpec) : Prop :=
  (cn.1 : ℝ) / (cn.2 : ℝ) ≤ (((y.round s c).error.val : ℚ) : ℝ)

/-- What a plan holds of a round with a verifier's message under the scope `.once`. -/
theorem round_once (s : Setting) (n : String) (w : ErrorKind) (e : Bound) (d : Draws) (b r a : ℕ) :
    ((RoundSpec.said n w e d b r a).round s .once).error = e.error ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.msg = b ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.drawE = d.drawE ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.drawNZ = d.drawNZ ∧
    ((RoundSpec.said n w e d b r a).round s .once).entry.work = s.workOf w .once := by
  simp [RoundSpec.round, RoundSpec.bound]

/-- A round that fits is covered. -/
theorem fits_covered (s : Setting) (q : ℕ) (cn : ℕ × ℕ) (n : String) (w : ErrorKind) (e : Bound)
    (d : Draws) (b r a : ℕ) (h : Fits q cn (.said n w e d b r a)) (hn : 0 < cn.2)
    (g : e.bad = false) : Covered s .once cn (.said n w e d b r a) := by
  obtain ⟨_, a', b', hb, rfl, hab⟩ := h
  unfold Covered
  rw [(round_once s n w _ d b r a).1]
  refine le_trans (le_of_eq ?_) (Bound.le_errorR (Bound.enclR_ratio a' b') g)
  have hn' : (cn.2 : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hb' : (b' : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [div_eq_div_iff hn' hb']
  exact_mod_cast hab

/-- The same relation at equal members of two lists of one length. -/
theorem forall₂_replicate {α β : Type} {R : α → β → Prop} {x : α} {y : β} (h : R x y) :
    ∀ k : ℕ, List.Forall₂ R (List.replicate k x) (List.replicate k y)
  | 0 => .nil
  | k + 1 => .cons h (forall₂_replicate h k)

end Cb.Pv

#print axioms Cb.Pv.round_once
#print axioms Cb.Pv.fits_covered
