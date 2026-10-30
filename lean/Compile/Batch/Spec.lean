-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Spec.lean: for the compiled scheme: `alphaB`, the first term of the completeness bound
`alphaBG` (Compile/Batch/SpecGrind.lean; at a wire with `W.OK` the whole bound: `alphaBG_of_ok`,
CompileK/Counts.lean), and the type `LifeWB`. Definitions only. (Words of this library:
lean/GLOSSARY.md.)

This file does not state the three properties of the scheme.

  `alphaB`   pT + pL + N pO: a batch fails if the verifier randomness of Test, of the sampled copy's
             Link or of a slot is withheld; a union bound over the slots
  `LifeWB`   the challengers with the calls and replies of the lifetime experiment (`LifeOutB`,
             `LifeInB`: Compile/Batch/SpecLifeStar.lean)

(`extractorB`, `tVB`, `epsB`: Compile/Batch/SpecBinding.lean.)

The format: `L.onlineBatch.ann.Fmt` (Iop/BatchFmt.lean) is a hypothesis of theorems on the compiled schemes
(for example Compile/Batch/PubProgMainBGr.lean: `mainBatchKEGrWithBOf`): `Iop.BatchProtocol.Props` does not
contain it. `Fmt` asks that the kinds of the rounds run local, shared, local, and that a component
that the format of a round does not send is trivial and has no oracle position. The compiled
verifier rejects other patterns of rounds, and the prover's verifier message in a round without
format is not uniform.

Notation: `L.maxBatchSize` (N above): a natural number, "the number of slots" (`BatchProtocol`, Iop/Batch.lean); `M`: an
`LH.Nums`, "All numbers of the interface." (Iop/InteractiveOracleProof.lean); `M.pT`, `M.pL`, `M.pO` (pT, pL, pO
above): numbers in ℝ≥0∞; in `BatchProtocol.Complete` (Iop/Batch.lean: its fields `prT`, `prL`, `prB`) each
stands as a bound on `prRho` of a set `Honest.withheld` (Iop/InteractiveOracleProof.lean).
-/
import Compile.Batch.Counts
import Compile.Batch.SpecBinding
import Iop.BatchFmt
import Compile.Batch.SpecGlue
import Compile.Batch.SpecLifeStar

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

instance : Inhabited (IVK lam L) := ⟨⟨default, none⟩⟩
instance : Inhabited (Prf lam L) := ⟨⟨0, default, none, none⟩⟩

/-! ## The bound -/

def alphaB (L : BatchProtocol I X) (M : LH.Nums) : ℝ≥0∞ := M.pT + M.pL + L.maxBatchSize * M.pO

/-! ## The type -/

abbrev LifeWB (W : QueryLayout lam L) : Type 1 := World (spec lam W.K L) (LifeOutB X) (LifeInB L)





end Compile.Batch
