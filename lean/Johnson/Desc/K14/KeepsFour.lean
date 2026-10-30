-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/KeepsFour.lean: the functions of Johnson/Desc/K14/Text.lean keep four relations
together: "a statement only grows", "no new mark", "Linked stays", "a marked group keeps its mark,
its members and its open rows". Theorems: corollaries of Johnson/Desc/K14/Keeps.lean (each of these
functions keeps every relation that the ground's plain functions keep) at groundKeeps_four.

  Four a b           the four.
  page_keeps_four    linPoint · laysRec · loc · joins · linZeta · split · behindU · behindOmega.
What is not claimed. "A sampled message's sample rows stay" (Johnson/Desc/Ground/Begin.lean) is not
among the four: it follows in the same way, at groundKeeps_kept. The four do not exclude a message
that is made a member before it is sampled (see Johnson/Desc/Ground/Linked.lean's head). Nothing on
the blocks that call these functions. Nothing on soundness.

-/
import Johnson.Desc.K14.Keeps
import Johnson.Desc.Ground.LinkedKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14
open OnBytes OnBytes.Params Desc.Plain VerifiableInference.Desc VerifiableInference.Desc.Ground

/-- The four relations together. -/
abbrev Four (a b : Statement) : Prop :=
  (Grows a b ∧ NoNewMark a b) ∧ (KeepsLinked a b ∧ Frozen a b)

/-- **Each of the eight functions of Johnson/Desc/K14/Text.lean that return a state keeps all
four.** -/
theorem page_keeps_four (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (ids : Array Nat) :
    (linPoint p d rs = some d' → Four d.st d'.st) ∧ (laysRec p d rs = some d' → Four d.st d'.st) ∧
    (loc p d rs gs = some d' → Four d.st d'.st) ∧ (joins p d rs = some d' → Four d.st d'.st) ∧
    (linZeta d rs = some d' → Four d.st d'.st) ∧ (split p d rs = some d' → Four d.st d'.st) ∧
    (behindU p d ids = some d' → Four d.st d'.st) ∧
    (behindOmega p d ids = some d' → Four d.st d'.st) :=
  ⟨linPoint_keeps groundKeeps_four p d d' rs, laysRec_keeps groundKeeps_four p d d' rs,
   loc_keeps groundKeeps_four p d d' rs gs, joins_keeps groundKeeps_four p d d' rs,
   linZeta_keeps groundKeeps_four d d' rs, split_keeps groundKeeps_four p d d' rs,
   behindU_keeps groundKeeps_four p d d' ids, behindOmega_keeps groundKeeps_four p d d' ids⟩

end Desc.K14
