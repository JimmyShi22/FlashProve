-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadO.lean: three facts on the relation `agF W` (Compile/Batch/SpecOneCall.lean: two
answers that are both failed proof-of-work attempts, not the last), for oracle algorithms (words of
this library: lean/GLOSSARY.md).

  `onlyFb_agF`  `agF W` relates no two answers but at the Fiat-Shamir oracles `fb t` and their ghost
                names `fbw t j` (`OnlyFb`, Compile/Batch/DeadFrame.lean).
  `facF_realQ`  `FactorsBy (agF W)` (related answers have the same continuation) passes from c to
                `realQ c` (Compile/Batch/Oracles.lean), which queries `fb t` for `fbw t j`: at a
                ghost name `fbw t j` the relation says what it says at `fb t`.
  `agF_seed`  At the auxiliary oracle `other` it relates nothing, so related answers are equal: what
              `OComp.FactorsBy.derive` needs of the seed's oracle.

The property under bind, map, blocks and derive is generic in the relation: Rom/OverOneN.lean,
Rom/OverOneNGen.lean, Rom/OverOneNDerive.lean.

Notation:
  `agF W` (Compile/Batch/SpecOneCall.lean): the relation on typed answers: at `fb t` or `fbw t j`:
    `failsAt` of both answers (a failed attempt that is not the last); at every other oracle no two
    answers are related;
  `OComp.FactorsBy ag c` (Rom/OverOneN.lean): the program reads an answer only up to a relation ag
    on answers: at every query node, answers in the relation have the same continuation program; and
    so on in every continuation.

Limits: nothing on any program of the scheme.
-/
import Compile.Batch.DeadFrame
import Compile.Batch.RealQ

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem onlyFb_agF (W : QueryLayout lam L) : OnlyFb (agF W) := fun o _ _ _ h => by
  cases o with
  | fb t => exact .inl ⟨t, rfl⟩
  | fbw t j => exact .inr ⟨t, j, rfl⟩
  | _ => exact h.elim

/-- `FactorsBy (agF W)` passes from c to `realQ c`. -/
theorem facF_realQ (W : QueryLayout lam L) {α : Type} (c : TypedOracleComputation lam W.K L α) (h : c.FactorsBy (agF W)) :
    (realQ c).FactorsBy (agF W) := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r (h r)
  | query o q k ih =>
    cases o <;> exact ⟨fun r r' e => congrArg realQ (h.1 r r' e), fun r => ih r (h.2 r)⟩

/-- at the seed's oracle `other` answers that the relation relates are equal (it relates none) -/
theorem agF_seed (W : QueryLayout lam L) (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other) :
    ∀ q r r', agF W σ.o q r r' → r = r' := by
  rw [hσ]
  exact fun _ _ _ h => h.elim

end Compile.Batch.Dead
