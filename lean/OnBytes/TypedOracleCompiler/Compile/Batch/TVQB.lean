-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/TVQB.lean: `tVQB`, the one term of the library's
Compile/Batch/SpecBinding.lean that GlueTools.lean needs, in a file of its own, so that this folder
does not rest on the honest prover.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Events

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The number of queries of the verifier of one slot: one for each round, and one more to g in the
joining round; a leaf and a path for each opening; a leaf and a path in the request tree. -/
def tVQB {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) : ℕ :=
  (Q.loc.shape.length + 1) + (wq.nOpen * (wq.maxDepth + 1) + (depthReq + 1))

end TypedOracleCompiler.Compile.Batch
