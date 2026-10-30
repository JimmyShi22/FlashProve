-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookRounds.lean: the rounds of a lookup, as the plan's entries: the
planner's own term at the lookup's shape. One definition, with code. No theorem.

Main names:
  `lookEntries set h`: **the lookup's rounds**: who sends how much, what is drawn, under which name:
    `Params.planForest` (OnBytes/Params/SubRounds.lean:43, over `planLookup`,
    OnBytes/Params/Planner.lean:428-446) at the shape's two depths, for several calls.

Limits: it asks the planner for the list (`Params.finish`, at the scope of a request), not for its
verdict on the rounds' errors (`finishHeld`). That the list is the plan's stretch at a place is
asked where a file's description is held against its plan. Nothing has been shown of it.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Model.Forest
import OnBytes.Params.SubRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes

/-- **The lookup's rounds**: the plan's entries of a lookup of shape h with several calls, by the
planner's own term. set: the plan's setting. Nothing where the planner refuses. -/
def lookEntries (set : Params.Setting) (h : Model.Forest.Shape) : Option (List Fmt.Entry) :=
  match Params.finish set .request (Params.planForest { v := h.v, d := h.d, shifted := true }) with
  | .ok p => some (p.rounds.map (·.entry))
  | .error _ => none

end VerifiableInference.Desc.First.Look
