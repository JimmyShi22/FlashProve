-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySeatNumsW2.lean: THEOREMS. W's message AT THE LIBRARY's SHAPE AND THE LIBRARY's RADIUS. KeySeatNumsW.lean typed a shape shW of its own and called honest_pins_at at 3145534, the largest radius that the test meetsB passes. THE LIBRARY HAS THE SHAPE ALREADY (Johnson.Top.H.shW, Johnson/Top/H/KeyFamilies.lean:115-116) AND ITS SIGNATURE's RADIUS IS 3138896 (:132). Here: the two shapes are one (by rfl): ours is a twin · meetsB at 3138896, by the kernel · the corollary at the library's shape and radius.
OBJECT: Johnson.Top.H.csKey · Johnson.Top.H.shW · 3138896. USER: none. Nothing on soundness.

-/
import Johnson.RunOne.KeySeatNumsW
import Johnson.Top.H.KeyFamilies

set_option autoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K1
open Johnson.Top.H (csKey)

/-- Our shape of W's message is the library's. -/
theorem shW_landed : shW = Johnson.Top.H.shW := rfl

theorem tieWH : Tie csKey Johnson.Top.H.shW := tieW
theorem meetsWH : meetsB csKey Johnson.Top.H.shW 3138896 = true := by decide +kernel

/-- **honest_pins_at at the library's shape of W's message and its signature's radius.** -/
theorem honest_full_wH {XI : Type} (F : FileDescription XI) (tag : String) (j₀ t₀ : ℕ) (hfit : seatFaultAt F csKey tag Johnson.Top.H.shW j₀ t₀ = none) :
    HonestAt F csKey Johnson.Top.H.shW 3138896 j₀ t₀ :=
  fun _ _ h o ρ => honest_pins_at F tag j₀ t₀ hfit tieWH meetsWH h o ρ

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.shW_landed
#print axioms Johnson.RunOne.KeyLetters.tieWH
#print axioms Johnson.RunOne.KeyLetters.meetsWH
#print axioms Johnson.RunOne.KeyLetters.honest_full_wH
