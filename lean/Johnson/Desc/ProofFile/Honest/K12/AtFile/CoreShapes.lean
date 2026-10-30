-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/CoreShapes.lean: the public numbers of the last chain's test's members,
at the written sendings: the index masks' message, W's message, Omega's.

  `memsOf`         the members' public numbers, as `jobW` lays them at a list of shapes
  `memsW`          at the three written shapes

Limits. Public numbers alone. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.K1.Law.TiesWritten
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open VerifiableInference.Desc.K1 (realSized parGF parWF)
open Johnson.Prover.Send (shapeAt)

/-- The members' public numbers, as `jobW` lays them at a list of shapes. -/
def memsOf (l : List OnBytes.OracleShape) : List ProofFile.Honest.K12.Light.MemShape :=
  (l.zipIdx).map fun x =>
    ProofFile.Honest.K12.AtProof.memShape x.1 ((ProofFile.Honest.K12.Light.firstsOf l).getD x.2 (none, none))

/-- The three written sendings' shapes, at the sized record. -/
def shapesW (x : OnBytes.Params.LinShape) : List OnBytes.OracleShape :=
  [shapeAt parGF (parGF.sent.size - 1), shapeAt parWF 0,
    ((Desc.K14.withOmega x).getD 0 default).shape]

/-- **The members' public numbers at the written sendings.** -/
def memsW : List ProofFile.Honest.K12.Light.MemShape :=
  (realSized.map fun q => memsOf (shapesW q.1.shape)).getD []

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.memsOf
#print axioms ProofFile.Honest.K12.AtFile.shapesW
#print axioms ProofFile.Honest.K12.AtFile.memsW
