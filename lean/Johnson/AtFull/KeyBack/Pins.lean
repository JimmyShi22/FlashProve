-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/Pins.lean: WHAT THE KEY FILE's BACK READS OF m, AS EQUATIONS TO WRITTEN
VALUES. One structure, and what follows from its fields at once. It shows the equations of no m.

`Key.sourceOf`, `Key.rangesNumbers` and `Key.laterPlaces` (Johnson/Desc/Key/Desc.lean,
Ranges.lean, Places.lean) read of m: the key file's three chains' sendings; their three plans; the
planner's sized key and setting; the planner's three priced plans; the number of the ranges'
stages in the chains as read. `KeyPins m` says that each of these is the full size's written
value. It is the seam between two kinds of files: closed facts at the written values, which name
no m; and whoever shows, from the road that makes m, that m has these values.

  `KeyPins m`: the eight equations.
  `KeyPins.shape`, `KeyPins.rounds₀`, `KeyPins.rounds₁`, `KeyPins.rounds₂`: the shape and the
    plans' rounds, by rewriting.
Limits. THAT `KeyPins` HOLDS AT ANY m IS NOT SHOWN HERE. It pins what the three routines READ.
What `Key.sourceOf` lays into its answer unread (the chains as read, whole; the planner's chains,
whole; the layout's units) is not pinned: later rows that read these of X want pins of their own.
That the written values are the planner's at any public files is not said here.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core
import Johnson.G.SendsWritten
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open Johnson.G (keySends0 keySends1 keySends2)
open VerifiableInference.Number.ByRuns (keyThree)
open Lk6.AtPlan (keyFull)

/-- **What the key file's back reads of m is the full size's written value.** -/
structure KeyPins (m : Made) : Prop where
  /-- the three chains' codes and sendings -/
  sends : m.key = (keySends0, keySends1, keySends2)
  /-- the three chains' plans, as the chains' parameters bear them -/
  p₀ : plan₀ m = keyThree.A.plan.plan
  p₁ : plan₁ m = keyThree.B.plan.plan
  p₂ : plan₂ m = keyThree.C.plan.plan
  /-- the planner's sized key and setting -/
  sizedKey : m.p.chains.made.sized.key = keyFull
  sizedSet : m.p.chains.made.sized.set = recordSet
  /-- the planner's three priced plans -/
  madeKey : m.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan]
  /-- the number of the ranges' stages, in the chains as read -/
  rangesLen : m.p.chains.key.oneTime.ranges.stages.length = keyFull.ranges.x.stages.length

namespace KeyPins
variable {m : Made}

theorem shape (h : KeyPins m) : shapeK m = keyFull.once.shape := by
  show m.p.chains.made.sized.key.once.shape = _
  rw [h.sizedKey]

theorem rounds₀ (h : KeyPins m) : (plan₀ m).rounds = keyThree.A.plan.plan.rounds := by rw [h.p₀]
theorem rounds₁ (h : KeyPins m) : (plan₁ m).rounds = keyThree.B.plan.plan.rounds := by rw [h.p₁]
theorem rounds₂ (h : KeyPins m) : (plan₂ m).rounds = keyThree.C.plan.plan.rounds := by rw [h.p₂]

end KeyPins

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.KeyPins.shape
#print axioms Johnson.AtFull.KeyBack.KeyPins.rounds₀
#print axioms Johnson.AtFull.KeyBack.KeyPins.rounds₁
#print axioms Johnson.AtFull.KeyBack.KeyPins.rounds₂
