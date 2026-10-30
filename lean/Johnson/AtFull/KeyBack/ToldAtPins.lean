-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldAtPins.lean: `Key.toldOfMade m` RETURNS THE WRITTEN TABLE
`Johnson.KB4.toldKeyFull`, FROM THE PINS AND THE LABELS' GROUPS. Calls alone.

What stays as premises:
  `KeyPins m` (Pins.lean): SHOWN AT NO m HERE.
  hg₀, hg₁, hg₂: `Key.groupsAtLabel` at the written sendings' labels gives `groupsA`, `groupsB`,
    `groupsC`. The three are proved in Johnson/AtFull/KeyBack/LabelsKey.lean; they are
    handed in by ToldOfKeyPins.lean.
What is paid: that the routine returns (`toldOfMade_returns`, ToldLaw.lean, over `treesK_at_pins`,
TreesKAtPins.lean); what it returns (`toldOfMade_eq`, ToldValue.lean; `toldVal_eq`, ToldRun.lean);
that this is the written table (`told_A`, `told_B`, `told_C`).
Limits. No m is shown at which `KeyPins` holds. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ToldAtA
import Johnson.AtFull.KeyBack.ToldAtB
import Johnson.AtFull.KeyBack.ToldAtC
import Johnson.AtFull.KeyBack.ToldLaw
import Johnson.AtFull.KeyBack.TreesKAtPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G (ChainSends Sending keySends0 keySends1 keySends2)
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)

/-- **r1's table at the written value, from the pins and the labels' groups.** -/
theorem toldOfMade_at_pins (m : Made) (h : KeyPins m)
    (hg₀ : (keySends0.sends.map (·.label)).map groupsAtLabel = groupsA)
    (hg₁ : (keySends1.sends.map (·.label)).map groupsAtLabel = groupsB)
    (hg₂ : (keySends2.sends.map (·.label)).map groupsAtLabel = groupsC) :
    toldOfMade m = .ok Johnson.KB4.toldKeyFull := by
  have k0 : m.key.1 = keySends0 := by rw [h.sends]
  have k1 : m.key.2.1 = keySends1 := by rw [h.sends]
  have k2 : m.key.2.2 = keySends2 := by rw [h.sends]
  have hr := toldOfMade_returns m _ _ _ (treesK_at_pins m h)
  rw [toldOfMade_eq m groupsA groupsB groupsC 1 0 0
    (by rw [h.p₀]; exact fits_A.offset) (by rw [h.p₁]; exact fits_B.offset)
    (by rw [h.p₂]; exact fits_C.offset) (by rw [k0]; exact hg₀) (by rw [k1]; exact hg₁)
    (by rw [k2]; exact hg₂) hr, k0, k1, k2, h.shape, h.rounds₁, toldVal_eq, toldVal_eq, toldVal_eq,
    told_A, told_C]
  rw [show toldRun keySends1 groupsB 0
      (ownMasks keySends1.codes keyFull.once.shape
        VerifiableInference.Number.ByRuns.keyThree.B.plan.plan.rounds)
      (heldMask keyFull.once.shape) = Johnson.KB4.told2 from told_B]
  rfl

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.toldOfMade_at_pins
