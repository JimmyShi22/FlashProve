-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoKeepsOf.lean.
The properties Keeps and KeepsL, applied to a run.

`Keeps.of h hS (by keeps)`: from a run h of a routine, from a state with the slots' arrays at their
sizes: the state that it left is a later state, with the arrays at their sizes. `KeepsL.of`: the
same for a routine of a link.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLink

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem Keeps.of {α : Type} {x : SubM α} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x F c = .ok ((a, G), c')) (hS : Sized F) (hk : Keeps x) : Later F G ∧ Sized G :=
  hk _ _ _ _ _ h hS

theorem KeepsL.of {α : Type} {x : LinkM α} {Lc Lc1 : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x Lc F c = .ok (((a, Lc1), G), c')) (hS : Sized F) (hk : KeepsL x) :
    Later F G ∧ Sized G :=
  hk Lc _ _ _ _ _ h hS

end Fo
