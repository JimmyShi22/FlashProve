-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/PinsOfMade.lean: Pins (Pins.lean) gathered at what Key.sourceOf returns: from
the return itself and plain equations on m, the planner's answer with the sendings. It serves
key_planOk_at_made (RowAtMade.lean). By unfolding and rewriting; nothing is evaluated.

  pins_of_made (r1 : Key.sourceOf m = .ok X) ... : Pins X N P.
The premises, each an equation about m, and what is meant to give it.
  r1: that the source is made. hD, hT: that the declared rounds and the tenants as told which
  declKOf and Key.toldOfMade return are the written ones: whatever shows what Key.sourceOf returns.
  hz, hs, c1, c2, c3: the sized key, the setting and the three sendings' codes: IM.keyPins_at_made
  and IM.keyPlans_at_made.
  i1 to i7: the seven items as read back: Johnson.KB9.items_at_made.
  p1, p2, p3, pk: the plans as read back and as made: IM.keyPlans_at_made.
  hN, hP: the places' numbers: whatever shows what Key.rangesNumbers and Key.laterPlaces return.
Limits. Every premise is owed by another file. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Pins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open OnBytes.Params (exc_bind)
open Johnson.G.OfPlan (Made)
open Lk6.AtPlan (keyFull)
open VerifiableInference.Number.ByRuns (keyThree)
open Johnson.KB8 (declKeyFull rangesNumsFull laterPlacesFull)

theorem pins_of_made {m : Made} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (r1 : sourceOf m = .ok X) (hD : Johnson.G.OfPlan.declKOf m = .ok declKeyFull)
    (hT : toldOfMade m = .ok toldKeyFull) (hz : m.p.chains.made.sized.key = keyFull)
    (hs : m.p.chains.made.sized.set = recordSet) (c1 : m.key.1.codes = keyFull.codes)
    (c2 : m.key.2.1.codes = keyFull.codes) (c3 : m.key.2.2.codes = keyFull.codes)
    (i1 : m.p.chains.key.oneTime.indexMasks = keyFull.once.input)
    (i2 : m.p.chains.key.oneTime.ranges = keyFull.ranges.x)
    (i3 : m.p.chains.key.oneTime.binding = keyFull.binding)
    (i4 : m.p.chains.key.oneTime.codes = keyFull.codes)
    (i5 : m.p.chains.key.oneTime.lin = keyFull.once.shape)
    (i6 : m.p.chains.key.shared.codes = keyFull.codes)
    (i7 : m.p.chains.key.shared.lin = keyFull.once.shape)
    (p1 : m.p.chains.key.oneTime.given.plan = keyThree.A.plan.plan)
    (p2 : m.p.chains.key.shared.given.plan = keyThree.B.plan.plan)
    (p3 : m.p.chains.key.second.given.plan = keyThree.C.plan.plan)
    (pk : m.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan])
    (hN : N = rangesNumsFull) (hP : P = laterPlacesFull) : Pins X N P := by
  unfold sourceOf at r1
  obtain ⟨D, h1, r1⟩ := exc_bind r1
  obtain ⟨T, h2, r1⟩ := exc_bind r1
  obtain rfl : D = declKeyFull := Except.ok.inj (h1.symm.trans hD)
  obtain rfl : T = toldKeyFull := Except.ok.inj (h2.symm.trans hT)
  obtain rfl : _ = X := Except.ok.inj r1
  exact
    { idx := i1, ranges := i2, binding := i3, codes₁ := i4, lin₁ := i5, codes₂ := i6, lin₂ := i7
      plan₁ := p1, plan₂ := p2, plan₃ := p3
      cutShape := congrArg (·.once.shape) hz
      cutCodes := by
        show (m.key.1.codes, m.key.2.1.codes, m.key.2.2.codes) = _
        rw [c1, c2, c3]
      cutIdx := congrArg (·.once.input) hz
      cutRanges := congrArg (·.ranges.x) hz
      cutSamples := congrArg (·.samples) hs
      D := rfl, told := rfl
      set := congrArg (·.set) hz
      sized := hz, plans := pk, same := rfl, N := hN, P := hP }

end Johnson.KB4

#print axioms Johnson.KB4.pins_of_made
