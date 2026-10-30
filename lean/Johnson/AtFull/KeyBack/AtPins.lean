-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/AtPins.lean: r2 AND r3 OF THE KEY FILE's BACK AT THE WRITTEN VALUES, FROM
`treesSent`'s RETURNS, THE PINS, AND FACTS ON THE TREES. The closed facts on the written plans and
the typed sizes are paid (BatAt0, FreeAt0, GuardAt0, CutAtU, CutAtW; that the typed shape splits:
`OnBytes.Params.keyOnce_sharedSplit`, OnBytes/Params/KeyOnceFacts.lean); calls alone.

IT TAKES A RETURN TO GIVE A RETURN. What stays as premises, none of it shown at any m here:
  `treesSent`'s returns at the key file's chains (one for r2, three for r3);
  `KeyPins m` (Pins.lean): what the routines read of m is the full size's written value. Of its
    fields r2 uses the first plan, the sized key and the setting; r3 the sized key, the setting,
    the made plans and the number of the ranges' stages as read back;
  facts on the trees that `treesSent` returns: which trees each place's first opening reads, and
    that the first chain sends six. They are closed once the trees are named.
  `rangesNumbers_at_pins`: `Key.rangesNumbers m = .ok Johnson.KB8.rangesNumsFull`.
  `laterPlaces_at_pins`: `Key.laterPlaces m = .ok Johnson.KB8.laterPlacesFull`.
Limits. No m is shown at which the premises hold. The trees' shapes in the premises were typed by
hand in Johnson/HB/LLHARD/KB8/Written.lean: where one is wrong, its premise can be met by no m at
which the routine returns, and the law is idle. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.AtWritten
import Johnson.AtFull.KeyBack.Pins
import OnBytes.Params.KeyOnceFacts
import Johnson.AtFull.KeyBack.BatAt0
import Johnson.AtFull.KeyBack.FreeAt0
import Johnson.AtFull.KeyBack.GuardAt0
import Johnson.AtFull.KeyBack.CutAtU
import Johnson.AtFull.KeyBack.CutAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open VerifiableInference.Number.ByRuns (keyThree)
open Lk6.AtPlan (keyFull)

/-- **r2 at the written value, from one return, the pins and one fact on the trees.** -/
theorem rangesNumbers_at_pins (m : Made) (t₀ : List (Sent × Nat)) (h : KeyPins m)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (hfirst : rangesFirst t₀ = [(⟨22, 77, false, 1⟩, .own 1)]) :
    rangesNumbers m = .ok Johnson.KB8.rangesNumsFull := by
  have hA : (plan₀ m).rounds = roundsA := h.rounds₀
  have hg : rangesGuard m 18805 = true := by
    unfold rangesGuard
    rw [hA, h.sizedKey]
    exact guard_A
  rw [rangesNumbers_eq m t₀ 18805 h₀ (by rw [hA]; exact bat_first_A) hg,
    rangesAt_written m t₀ 18805 h.sizedKey h.sizedSet rfl hfirst (by rw [hA]; exact free_A)]

/-- **r3 at the written value, from three returns, the pins and four facts on the trees.** -/
theorem laterPlaces_at_pins (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (h : KeyPins m)
    (h₀ : treesSent "key file, first chain" m.key.1 (plan₀ m) [] = .ok t₀)
    (h₁ : treesSent "key file, shared chain" m.key.2.1 (plan₁ m)
      (ownMasks m.key.2.1.codes (shapeK m) (plan₁ m).rounds) = .ok t₁)
    (h₂ : treesSent "key file, second chain" m.key.2.2 (plan₂ m) [] = .ok t₂)
    (hfU : foldedFirst keyFull.once.shape t₁ =
      [(⟨24, 324, false, 0⟩, .own 0), (⟨13, 3, false, 2⟩, .own 2)])
    (hfO : ((sharedOpens keyFull.once.shape t₁)[2 + (switchOpens 0 .folded t₁).length]?).map
        (fun x => (x.1.dropLast, 0)) =
      some ([(⟨22, 36, false, 1⟩, .own 1), (⟨13, 3, false, 2⟩, .own 2)], 0))
    (hfW : ownFirst keyFull.once.shape t₀ t₁ =
      [(⟨13, 3, false, 0⟩, .taken 0 0), (⟨22, 12, false, 5⟩, .taken 0 5),
        (⟨22, 36, false, 1⟩, .taken 1 1)])
    (hn : t₀.length = 6) :
    laterPlaces m = .ok Johnson.KB8.laterPlacesFull :=
  laterPlaces_written m t₀ t₁ t₂ keyThree.B.plan keyThree.C.plan h₀ h₁ h₂ h.sizedKey h.sizedSet
    h.rangesLen (by rw [h.madeKey]; rfl) (by rw [bats_B]; rfl) (by rw [bats_B]; rfl) cutU_B cutO_B
    rootsU_B rootsO_B (by rw [h.madeKey]; rfl) bat_first_C cutW_C hfU
    OnBytes.Params.keyOnce_sharedSplit hfO hfW hn

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rangesNumbers_at_pins
#print axioms Johnson.AtFull.KeyBack.laterPlaces_at_pins
