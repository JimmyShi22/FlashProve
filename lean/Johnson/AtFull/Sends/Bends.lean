-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/Bends.lean: FIVE BENDS OF A WRITTEN CHAIN OF SENDINGS, for controls that bite:
each turns ONE THING INSIDE THE LIST OF SENDINGS and leaves the chain's file, number and codes as
they are.
Definitions alone.
  `bendsOf C`: the last sending's number of its entry raised by one · the first sending's label
    lengthened by a sign · the middle sending's list of what is sent emptied · the middle sending's
    entry behind exchanged for its own seed's entry · the last sending dropped.
  `noneOf r Cs`: r returns, and what it returns is none of the chains Cs (by `sameChain`).
Nothing on soundness.
-/
import Johnson.AtFull.Sends.ProofFirst

set_option autoImplicit false

namespace Johnson.AtFull.Sends

open VerifiableInference.PlanWritten Johnson.G
open OnBytes OnBytes.Params

/-- Five bends, each inside the list of sendings. -/
def bendsOf (C : ChainSends) : List ChainSends :=
  [ { C with sends := C.sends.mapIdx fun i s =>
        if i + 1 = C.sends.length then { s with entry := s.entry + 1 } else s },
    { C with sends := C.sends.mapIdx fun i s =>
        if i = 0 then { s with label := s.label ++ "x" } else s },
    { C with sends := C.sends.mapIdx fun i s =>
        if i = C.sends.length / 2 then { s with sent := [] } else s },
    { C with sends := C.sends.mapIdx fun i s =>
        if i = C.sends.length / 2 then { s with behind := s.seed } else s },
    { C with sends := C.sends.dropLast } ]

/-- It returns, and the chain is none of these. -/
def noneOf (r : Except String ChainSends) (Cs : List ChainSends) : Bool :=
  match r with
  | .ok a => Cs.all fun C => !sameChain a C
  | .error _ => false

end Johnson.AtFull.Sends
