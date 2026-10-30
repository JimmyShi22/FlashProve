-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/SeedNode.lean: `Seed.hNode`, one declaration of the library's
Compile/Batch/SeedCache.lean, said again with the same text over this folder's `typedOracleFamily`.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

It is here because the terms of one statement on entry files, written over this folder's oracles,
hold it; that statement is not in this folder. The rest of the library's file, which is on the
honest side, is not said again. `Seed.evalO` rests on no declaration of the library that this folder
says again: so the library's own serves.

Terms: lean/GLOSSARY.md.

-/
import Compile.Batch.SeedCache
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Seed
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
export _root_.Compile.Batch.Seed (evalO)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the node function of the trees over encoded indices under fixed oracle functions -/
def hNode {K : ℕ} (g : Fam (typedOracleFamily lam K L)) (a b : Dig lam) : Dig lam :=
  g OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits)

end TypedOracleCompiler.Compile.Batch.Seed
