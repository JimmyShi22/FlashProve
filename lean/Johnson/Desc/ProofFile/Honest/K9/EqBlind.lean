-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqBlind.lean: THE ONE Bool ON THE SHAPE AT "THE ONE EQUATION" (`oneShape`, Honest/K9/EqShape.lean) DOES NOT SEE WHAT
MOVES WITH THE PUBLIC FILES INSIDE THE GOALS' SCOPE: two whole shapes that are alike but for the calls' tables in the two components that
hold what a lookup heard (`strip a = strip a'`, Johnson/AtFull/Shape/Scope/Rel.lean) get the same answer.

  **`oneShape_blind`**   strip a = strip a' ⊢ oneShape a.1 = oneShape a'.1

By `oneShape_reads`: the Bool reads the link's context, the ledger and the core, which `strip` leaves. Limits. One equation between two
answers; that either is a yes is not proved here. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqShape
import Johnson.AtFull.Shape.Scope.Rel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open Johnson.AtFull.Shape (ShA)
open Johnson.AtFull.Shape.Scope (strip)

/-- **The Bool is blind to the calls' tables.** -/
theorem oneShape_blind {a a' : ShA} (h : strip a = strip a') : oneShape a.1 = oneShape a'.1 := by
  have h1 : a.1.link = a'.1.link := by
    have e := congrArg (fun z : ShA => z.1.link) h
    exact e
  have h2 : a.1.led = a'.1.led := by
    have e := congrArg (fun z : ShA => z.1.led) h
    exact e
  have h3 : a.1.core = a'.1.core := by
    have e := congrArg (fun z : ShA => z.1.core) h
    exact e
  exact oneShape_reads h1 h2 h3

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.oneShape_blind
