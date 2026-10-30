-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/LoopEager.lean: proof of `Spec.realQ_eager` (Compile/Batch/SpecLoop.lean): what
completeness needs of the search over nonces with the oracle functions fixed. (The statement for
lazily sampled oracles, `Spec.askW_law`, is proved in Compile/Batch/LoopLazy.lean.) (Words of this
library: lean/GLOSSARY.md.)
    `realQ_eager`      for fixed oracle functions f, `realQ c` (c with the ghost names written back:
                       queries to `fbw t k` turned into queries to `fb t`) under f is c under
                       `realF f`, which answers `fbw t k` as f answers `fb t`
                       (`fb t`, `fbw t k`: `OracleName`, Compile/Batch/Oracles.lean: `fb t`: Fiat-Shamir for
                       the protocol t; `fbw t k`, a ghost name: an oracle of the analysis:
                       proof-of-work attempt k + 1 is written as a query to `fbw t k`)
-/
import Compile.Batch.SpecLoop

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

theorem realQ_eager : Spec.realQ_eager := by
  intro I X lam K L α c f
  induction c with
  | pure a => rfl
  | sample n k ih => exact congrArg ((PMF.uniformOfFintype (Fin (n + 1))).bind) (funext ih)
  | query o q k ih => cases o <;> exact ih _

end Compile.Batch
