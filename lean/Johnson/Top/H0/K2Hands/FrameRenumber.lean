-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/FrameRenumber.lean: `renumber`, a frame with other numbers; `parts_alike`.
-/
import Johnson.Top.H0.K2Hands.FrameOfFront
import Johnson.Top.H.SwitchMapsCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes

/-- **A frame with other numbers**: g's number, and each kept member's old and new number, by its place
in the frame's list. All else stays. -/
def renumber (W : SwitchFrame) (g : ℕ) (olds anew : Array ℕ) : SwitchFrame :=
  { W with g := g, kept := W.kept.mapIdx fun i k =>
      { k with old := olds.getD i noId, anew := anew.getD i noId } }

section Point
variable {S S₀ : Statement} (hc : S.codes = S₀.codes) {o o₀ : ℕ}
  (e : (S.oracles[o]?).map (·.shape) = (S₀.oracles[o₀]?).map (·.shape))
include e

theorem shape_at : (S.oracles.getD o default).shape = (S₀.oracles.getD o₀ default).shape := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases h1 : S.oracles[o]? <;> cases h2 : S₀.oracles[o₀]? <;> simp [h1, h2] at e ⊢
  exact e

theorem rowBits_at (part : Part) : S.rowBits o part = S₀.rowBits o₀ part := by
  unfold Statement.rowBits
  cases h1 : S.oracles[o]? <;> cases h2 : S₀.oracles[o₀]? <;> simp [h1, h2] at e ⊢
  rw [e]

include hc

theorem placeBits_at (part : Part) : S.placeBits o part = S₀.placeBits o₀ part := by
  unfold Statement.placeBits
  cases h1 : S.oracles[o]? <;> cases h2 : S₀.oracles[o₀]? <;> simp [h1, h2] at e ⊢
  rw [e, hc]

theorem tableBits_at (part : Part) : S.tableBits o part = S₀.tableBits o₀ part := by
  unfold Statement.tableBits
  rw [rowBits_at e, placeBits_at hc e]

theorem padOf_at : padOf S o = padOf S₀ o₀ := by
  unfold padOf
  rw [hc, shape_at e]

end Point

/-- Two lists of messages' numbers, in two statements, with the same shapes place by place. -/
def Alike (S S₀ : Statement) (ks ks₀ : List ℕ) : Prop :=
  List.Forall₂ (fun o o₀ => (S.oracles[o]?).map (·.shape) = (S₀.oracles[o₀]?).map (·.shape)) ks ks₀

theorem pads_alike {S S₀ : Statement} (hc : S.codes = S₀.codes) : ∀ {ks ks₀ : List ℕ},
    Alike S S₀ ks ks₀ → ∀ init : Array ℕ × ℕ,
    ks.foldl (fun (s : Array ℕ × ℕ) o => (s.1.push s.2, s.2 + (padOf S o).length)) init =
      ks₀.foldl (fun (s : Array ℕ × ℕ) o => (s.1.push s.2, s.2 + (padOf S₀ o).length)) init
  | _, _, .nil, _ => rfl
  | _, _, .cons e t, init => by
    rw [List.foldl_cons, List.foldl_cons, padOf_at hc e]
    exact pads_alike hc t _

/-- **The parts of the rest feel no number.** -/
theorem parts_alike {S S₀ : Statement} (hc : S.codes = S₀.codes) {old old₀ : SingleRows}
    (h1 : old.code = old₀.code) (h2 : old.maskCode = old₀.maskCode) (h3 : old.masks = old₀.masks)
    (h4 : old.keptRows = old₀.keptRows)
    (hk : Alike S S₀ (switchKept old).toList (switchKept old₀).toList) :
    switchParts S old = switchParts S₀ old₀ := by
  unfold switchParts
  simp only [← Array.foldl_toList, pads_alike hc hk, hc, h1, h2, h3, h4]

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.parts_alike
