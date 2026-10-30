-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Oracles.lean: `Tag`, the tags of the three protocols, and `SymAny` (words of this library:
lean/GLOSSARY.md); `ON`, names of oracles, and `Prev`, how a Fiat-Shamir query starts, at one slot
with local rounds only. No definition reads `Prev`. The family of oracles of the compiled scheme,
with its own `OracleName`: Compile/Batch/Oracles.lean.
-/
import Iop.Wire
import Rom.Defer
noncomputable section -- Lean tags what it cannot compile

namespace Compile
open Iop Rom

/-! ## The oracles -/

inductive Tag | test | link | onl
  deriving DecidableEq
/-- `leaf`, `node`: the oracles of Merkle trees. `fs t`: one Fiat-Shamir oracle for each protocol.
`ann`: a query to it puts one digest on the trace. `other`: an auxiliary oracle on strings. -/
inductive ON | leaf | node | fs (t : Tag) | ann | other
  deriving DecidableEq

/-- a symbol of some prover oracle of a shape, with its position -/
def SymAny (s : Shape) : Type := Σ p : OPos s, OSym s p

variable {I X : Type}

/-- How a Fiat-Shamir query starts. Format (T1), `start`: digests, an optional request and a salt.
Format (T2), `tail`: a bit string, the chaining value of the answer before it. -/
inductive Prev (lam : ℕ) (X : Type)
  | start (cms : List (Dig lam)) (x : Option X) (salt : Bits)
  | tail (v : Bits)

end Compile
