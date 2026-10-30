-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/KnowStarDefs.lean: two small definitions beside the named witness extractor
(CompileK/KnowExt.lean).

Main names:
  `Phase.k`: the phase of a slot's chain without its values.
  `RootsOfChain.list`: the roots that are in the rounds' components (`RtC`, Compile/Batch/Verifier.lean: the
    shared one and the slot's), as a list.

Definitions only; nothing is claimed here.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowExt

set_option autoImplicit false

namespace Compile.Batch
open Iop

variable {lam : ℕ}

/-- The phase of a chain, without its values. -/
def Phase.k : Phase lam → PhK
  | .first => .first
  | .loc _ => .loc
  | .shr _ _ => .shr
  | .aft _ _ => .aft

/-- All roots of all components of all rounds. A component that is not sent, or that has no tree,
gives nothing. -/
def RootsOfChain.list : (s : Shape) → RootsOfChain lam s → List (Dig lam)
  | [], _ => []
  | _ :: s, (rt, rts) => rt.1.join.toList ++ rt.2.join.toList ++ RootsOfChain.list s rts

end Compile.Batch
