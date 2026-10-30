-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/MW.lean: three names for the closed facts of this folder: MW: the
joined written term writtenMade (Johnson/Goal/Written/Made.lean) with eight empty strings hung; radW
and topW: the two letters of Johnson.Bridge.OkNat.fiveOk at it, as numerals (that they are its
letters: Rads.lean, Top.lean). Definitions alone.
-/
import Johnson.Desc.Ok.FormRules
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofPlan.Every

/-- The written term with eight empty strings hung. -/
abbrev MW : OnBytes.Params.Configured :=
  VerifiableInference.PlanWritten.Joined.writtenMade.at Johnson.G.MadeFree.Hung.none

/-- The stored tables' radius at it. -/
abbrev radW : Nat := 2852142980

/-- The largest list at it. -/
abbrev topW : Nat := 967

end Johnson.AtFull.ProofPlan.Every
