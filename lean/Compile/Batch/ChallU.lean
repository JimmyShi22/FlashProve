-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ChallU.lean: a prover given by a program with tokens (Rom/Defer.lean). Definitions
(words of this library: lean/GLOSSARY.md).

  `PProg`  A prover's program: from the key with tokens and the instances to the proofs (for the
           compiled scheme: `Pp` of Compile/Batch/Star.lean, `PpU` of Compile/Batch/StarU.lean, with
           proof strings made for all requests).
  `progP pp`  The prover that pp gives. It is the erasure of pp (`erase`, Compile/Star.lean),
              started on the strings of the proving key; its queries to the ghost names `fbw`
              (Compile/Batch/Oracles.lean) stay as they are written. It is an object of the
              analysis. By rfl, `Ptok` of Compile/Batch/Star.lean is `progP` of `Pp`, and `PtokU` of
              Compile/Batch/StarU.lean is `progP` of `PpU`; the provers of the schemes are `realQ`
              of these (`realQ`, Compile/Batch/Oracles.lean: a query to fbw t k becomes the query to
              fb t at the same input).
  `Spec.InvD`  An invariant of a challenger's private state and the state of the experiment.

Limits: the game "which prover is it" and its challenger are not in this library.
-/
import Compile.Batch.StarU
import Compile.Batch.WithinVCB
import Rom.SpecCarryP

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Prob
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- a prover's program: from the key with tokens and the instances to the proofs -/
abbrev PProg (lam : ℕ) (L : BatchProtocol I X) (K : ℕ) : Type :=
  IskH lam L → List X → St lam K L (List (Prf lam L))

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- the prover that a program gives -/
def progP (pp : PProg lam L W.K) (k : ISK lam L) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (Gen.Slots (Prf lam L) b) :=
  (erase (pp k.1 (b.map Prod.fst)) k.2).bind fun o =>
    pure (fitLen ⟨0, default, none, none⟩ b.length o.1)




namespace Spec

/-- an invariant of a challenger's private state (as that of `VCBPG`, Compile/Batch/PubProg.lean)
and the state of the experiment: before the setup, the state is the initial one except for the
table; after it, the invariant of Compile/Batch/WithinVCB.lean, and: the setup has made at least one
token

An invariant with parameters, which a definition and theorems of other files use; it is not itself a
claim. -/
def InvD (W : QueryLayout lam L) (p : Params) : Option (IskH lam L × ℕ) → DSt (spec lam W.K L) → Prop
  | none, d => d = DSt.init _ ∨ ∃ T, d = { DSt.init _ with table := T }
  | some (k, N₀), d => Disc.WorldB.Inv W p (some (k, N₀)) d ∧ 0 < N₀


end Spec

end Compile.Batch
