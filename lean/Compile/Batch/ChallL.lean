-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ChallL.lean: the prover's program `PpL` of Compile/Batch/Mirror.lean, written as two
parts: the sampling of a copy (the copies: Compile/Batch/Star.lean), and the rest. `PpL` is in the
language that names the input of a marked query only at its release (`LStep`, Rom/DeferLate.lean)
(words of this library: lean/GLOSSARY.md).

  `PpLJ`  the batch, once the copy is sampled
  `PpL_eq`  `PpL` samples the copy and then runs `PpLJ`

Limits. This file defines no challenger. The challengers for batches in this language are `chalLBP`
and `chalLSBP` (Compile/Batch/PubChall.lean; definitions only): their reply to the first setup is pw
ivk (keyOf isk), for an arbitrary function pw.
-/
import Compile.Batch.Chall
import Compile.Batch.Mirror
import Compile.Step1_defc_L

noncomputable section

namespace Compile.Batch
open Iop Rom
open Compile.GlueB (GCall)
open Compile.DefC (virtL)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- the batch, once the copy is sampled: a sampled permutation of the slots (uniform if `WP.perm`
has `Enum.OK`, Iop/Wire.lean) places the requests, and the compiled prover runs once (if the key has
a copy number j; else no run) -/
def PpLJ (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : Fin (p.M + 1)) :
    Lp lam W.K L (List (Prf lam L)) :=
  (drawL WP.perm).bind fun σ => PpJL W WP p k fr xs j.val σ


/-- `PpL` samples the copy and then runs `PpLJ`. -/
theorem PpL_eq (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) :
    PpL W WP p k fr xs = LStep.sample p.M fun j => PpLJ W WP p k fr xs j := rfl

end Compile.Batch
