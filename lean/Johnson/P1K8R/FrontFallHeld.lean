-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FrontFallHeld.lean: THE SMALLNESS TEST: THE STATED SHARE OF ITS FIRST FALL
(`k8FrontFall`, `frontFallShare`: Johnson/Desc/ProofFile/Honest/K8/Falls.lean) IS HELD AGAINST THE
FALL's OWN TEST AT THE BATCHING's ROUND (`Fall.HeldOn`,
Johnson/Desc/ProofFile/Honest/Law/SharesFalls.lean), AT EVERY STATE WHOSE DATA ARE ALL LIVE, AT
STRINGS OF HASH BLOCKS AND AT TYPED CHALLENGES. A definition and lemmas; NONE OF THE LIBRARY's
GOALS. Nothing on completeness, soundness or hiding. An assembly: no new argument.

  `front_fall_val`, `front_fall_ok`   the value of `frontFallShare columns tau` is kapSl 128 ^ 3 *
      (columns * (tau - 1)) / p ^ 3; its denominator is not 0
  `liveOf columns tau s`   the state s holds data of the smallness test that are all live (no column
      of the drawn matrix is all 0), with that many columns and that tau
  **`front_fall_heldOn_blocks`**   d₂ a round's data that draws one field element and nothing else,
      its entry's positions of at most 64 bits: `Fall.HeldOn` of `k8FrontFall link o columns tau` at
      Run.ckP .two, [d₂] and `liveOf columns tau`
  **`front_fall_heldOn`**   the same at Run.ck .two: there the measure is at most columns * (tau -
      1) / p ^ 3, which is at most the share's value
By: `front_live`, `front_live_blocks` (Johnson/P1K8R/LiveOfFold.lean) · `fall_share_val`,
`fall_share_ok` (Johnson/P1K8R/DeadMark.lean) · one_le_kapSl (Iop/DrawOf.lean).
Limits. At a state with a column that is all 0 the test speaks at every challenge: that event is the
mark's (`deadMark`). That a state of a run meets `liveOf` is said in LiveOfFold.lean
(`state_of_fold`), of the verifier's fold. The uniform law on one round's messages is named, not
derived. No number is evaluated.
-/
import Johnson.P1K8R.LiveOfFold
import Johnson.P1K8R.DeadMark
import Johnson.Desc.ProofFile.Honest.Law.SharesFalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest (Odds Held Fall)
open ProofFile.Honest.K8 (allLive cols k8Front k8FrontFall frontFallShare)
open Iop
open scoped ENNReal

theorem front_fall_val (columns tau : ℕ) :
    (frontFallShare columns tau).val =
      kapSl 128 ^ 3 * ((columns * (tau - 1) : ℕ) : ℝ≥0∞) /
        ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) := fall_share_val columns tau

theorem front_fall_ok (columns tau : ℕ) : (frontFallShare columns tau).ok = true :=
  fall_share_ok columns tau

/-- The state holds data that are all live, with these sizes. -/
def liveOf (columns tau : ℕ) (s : S) : Prop :=
  ∃ tl, s.tl? = some tl ∧ allLive tl = true ∧ cols tl = columns ∧ tl.tau = tau

/-- **The stated share is held: at strings of hash blocks.** -/
theorem front_fall_heldOn_blocks (link o columns tau : ℕ) (d₂ : RDT)
    (h₂ : OneElem d₂.entry d₂.kind) (hl₂ : d₂.entry.logN ≤ 64) :
    (k8FrontFall link o columns tau).HeldOn (_root_.Run.ckP .two) [d₂] (liveOf columns tau) := by
  intro s hs
  obtain ⟨tl, hts, hlive, hc, ht⟩ := hs
  refine ⟨front_fall_ok columns tau, ?_⟩
  show Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d₂]) |
    (k8Front s (drawnT (_root_.Run.ckP .two) [d₂] ρ)).isSome = true} ≤
      (frontFallShare columns tau).val
  rw [front_fall_val, ← hc, ← ht]
  exact front_live_blocks s tl hts hlive d₂ h₂ hl₂

/-- **The stated share is held: at typed challenges.** -/
theorem front_fall_heldOn (link o columns tau : ℕ) (d₂ : RDT)
    (h₂ : OneElem d₂.entry d₂.kind) :
    (k8FrontFall link o columns tau).HeldOn (_root_.Run.ck .two) [d₂] (liveOf columns tau) := by
  intro s hs
  obtain ⟨tl, hts, hlive, hc, ht⟩ := hs
  refine ⟨front_fall_ok columns tau, ?_⟩
  show Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d₂]) |
    (k8Front s (drawnT (_root_.Run.ck .two) [d₂] ρ)).isSome = true} ≤
      (frontFallShare columns tau).val
  rw [front_fall_val, ← hc, ← ht]
  refine (front_live s tl hts hlive d₂ h₂).trans (ENNReal.div_le_div_right ?_ _)
  calc ((cols tl * (tl.tau - 1) : ℕ) : ℝ≥0∞) = 1 * ((cols tl * (tl.tau - 1) : ℕ) : ℝ≥0∞) :=
        (one_mul _).symm
    _ ≤ kapSl 128 ^ 3 * ((cols tl * (tl.tau - 1) : ℕ) : ℝ≥0∞) :=
        mul_le_mul' (one_le_pow₀ (one_le_kapSl 128)) le_rfl

end P1K8

#print axioms P1K8.front_fall_val
#print axioms P1K8.front_fall_ok
#print axioms P1K8.liveOf
#print axioms P1K8.front_fall_heldOn_blocks
#print axioms P1K8.front_fall_heldOn
