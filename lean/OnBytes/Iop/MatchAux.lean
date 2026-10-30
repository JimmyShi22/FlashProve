-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/MatchAux.lean: has Lean make, once, the congruence equations of two matchers of
OnBytes/Iop/Wf.lean and OnBytes/Iop/Lkp.lean.

Lean makes these equations on demand, in the module that first asks for them, together with helper
definitions (`….match_1.congr_eq_1._sparseCasesOn_3` and the like). Two modules that ask for them
apart each hold the helpers, and cannot then be imported together: a definition may stand in one
module alone. A module that imports this file finds them made.

No definition or theorem is written here by hand. No module at or below `OnBytes.Main` may import
this file: it runs a command of Lean's at build time, which the program's own source must not.

-/
import Lean.Meta.Match.MatchEqs
import OnBytes.Iop.Wf
import OnBytes.Iop.Lkp

open Lean Meta in
run_meta do
  discard <| Lean.Meta.Match.genMatchCongrEqns ``OnBytes.Wf.pendingOf.match_1
  discard <| Lean.Meta.Match.genMatchCongrEqns ``OnBytes.Lkp.keyTrees.match_1
