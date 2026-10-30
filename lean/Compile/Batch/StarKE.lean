-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarKE.lean: the compiled scheme with the entries in the verification key and no query
or tree for an empty slot. Definitions only. (Words of this library: lean/GLOSSARY.md.)

  `PKE`   the prover `PU` of Compile/Batch/StarU.lean, followed by the removal of the fields cm and
          piL from each proof, as in `argBK` (Compile/Batch/StarK.lean)
  `argBKE`   (C, `PKE`, V) with C and V of `argBK`

Differences from the implementation that it removes: the entries are in the verification key
(Compile/Batch/StarK.lean); those of Compile/Batch/ProverU.lean. Nothing is proved here.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.StarK
import Compile.Batch.StarU
import Rom.SpecCarryP

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

def PKE (k : ISK lam L) (b : List (X × Unit)) : TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  (PU W WP p k b).bind fun l => .pure (mapS stripK l)

def argBKE : Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) (ISK lam L) (PrfK lam L) :=
  withP (argBK W WP p) (PKE W WP p)

end Compile.Batch
