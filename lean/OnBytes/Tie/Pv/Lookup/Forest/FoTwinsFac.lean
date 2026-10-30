-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTwinsFac.lean.
The public factor of the padding, read in a commutative ring, is the plain function facK of
OnBytes/Tie/Pv/Lookup/Forest/FoPadFac.lean.

ok_callOf: under FoNums.ok h the call's number of a tree below NT is below 2^64. padKeyK_eq: the two
  plain forms of a call's padding key (OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean,
    OnBytes/Tie/Pv/Lookup/Forest/FoPadFac.lean) are one. fac_val': the fold by
  which Forest.draws makes the factor a, read by ρ, is Cb.Fo.PadFac.facK.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoPadFac

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model

/-- Under lawful public numbers a tree's call's number is a word. -/
theorem ok_callOf {h : Sh} (H : FoNums.ok h = true) (y : ℕ) (hy : y < h.NT) :
    h.callOf.getD y 0 < 2 ^ 64 := by
  obtain ⟨_, b, _, _, _, _, hN, _⟩ := Cb.Fo.ok_parts H
  have h1 : h.callOf.getD y 0 < h.NC := (b y hy).1
  omega

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The two plain forms of the padding key are one. -/
theorem padKeyK_eq (h : Sh) (θ : K) (c : ℕ) : Cb.Fo.PadFac.padKeyK h θ c = padKeyK h θ c := by
  unfold Cb.Fo.PadFac.padKeyK padKeyK OnBytes.Ends.tauN FoNums.tauN FoNums.t0Of
  rw [Array.getD_eq_getD_getElem?]
  cases h.calls[c]? <;> rfl

theorem fac_val' (h : Sh) (θ α : E) (hc : ∀ y, y < h.NT → h.callOf.getD y 0 < 2 ^ 64) :
    ρ.val ((List.range h.NT).foldl
      (fun a y => mulE a (powE (subE α (Forest.padKeyOf h θ (h.callOf.getD y 0))) (h.pub.getD y 0)))
      (powE (subE α (Forest.padKeyOf h θ 0)) h.emptyKeys)) = Cb.Fo.PadFac.facK h (ρ.val θ) (ρ.val α)
          := by
  rw [fac_val ρ h θ α hc]
  unfold Cb.Fo.PadFac.facK
  simp only [padKeyK_eq]

end
end Fo
