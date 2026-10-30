-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ValueSlotsFirst.lean: THE FIRST GROUP's VALUE WITH ITS SLOTS AND ORDERS LAID. The
twin of Johnson/Road/K4/ValueSlots.lean (`Plan4L`, `Plan4L.plan`) for the letters of the first group
(`Plan4F`, Johnson/Road/K4/CarriageFirst.lean). Definitions and five equations that hold by
definition.

  `Plan4LF`: the letters of `Plan4L`, and those that the first group has more: ls, nb, gB with their
    two conditions, and the request's tokens.
  `Plan4LF.planF`: a `Plan4F`: `Plan4L.plan`, but for two numbers. In the first group the
    embedding's hidden value is laid behind the routed gated layer's end values, at the slot that is
    the merge's first own slot in a later group (the formula f7); the merge's first own slot is the
    next. So sE := f7 and the field f7 := the formula f7 + 1. That K4's hearing lays them so:
    `hear_end_first` (Johnson/Road/K4/HearSlotsEnd.lean) with `slotsAt_k4Slots`
    (Johnson/Road/K4/SlotsTie.lean).
  `planF_D`, `planF_sE`, `planF_f7`, `planF_e5`, `planF_e6`: what was laid in.

Limits. A value: nothing is shown of it here beyond what was laid in. The number nI of the batched
sumcheck's end values stays a letter: the plan's NCL counts the embedding's claim in the first
group, and that one is not heard in the batched sumcheck (NCL − 1 are).
-/
import Johnson.Road.K4.ValueSlots
import Johnson.Road.K4.CarriageFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Inst.Model (Scl)

noncomputable section

/-- The letters that stay in the first group. -/
structure Plan4LF (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends Plan4L E M X where
  ls : ℕ
  nb : ℕ
  gB : ℕ
  hnb : nb ≤ 2 ^ gB
  hd : D.d = nb * 2 ^ ls
  /-- the request's tokens -/
  tok : X → ℕ → ℕ

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace Plan4LF
variable (Q : Plan4LF E M X)

/-- The letters of the first group's value. -/
def planF : Plan4F E M X where
  toPlan4 := { Q.toPlan4L.plan with f7 := Q.toPlan4L.slots.f7 + 1 }
  ls := Q.ls
  nb := Q.nb
  gB := Q.gB
  hnb := Q.hnb
  hd := Q.hd
  tok := Q.tok
  sE := Q.toPlan4L.slots.f7

theorem planF_D : Q.planF.D = Q.D := rfl

theorem planF_sE : Q.planF.sE = Q.toPlan4L.slots.f7 := rfl

theorem planF_f7 : Q.planF.f7 = Q.toPlan4L.slots.f7 + 1 := rfl

theorem planF_e5 : Q.planF.e5 = OnBytes.Tie.Pv.Lay.eRange _ Q.h5 := rfl

theorem planF_e6 : Q.planF.e6 = OnBytes.Tie.Pv.Lay.eRange _ Q.h6 := rfl

end Plan4LF
end
end OnBytes.Road.K4
