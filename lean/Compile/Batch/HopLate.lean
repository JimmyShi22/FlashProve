-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/HopLate.lean: the relation `RelB` between a challenger for batches in mode I
(Rom/Defer.lean) and its form in `LStep` (Rom/DeferLate.lean). Used in Compile/Batch/PubLate.lean
(closure, context Γ: the head of Compile/Batch/SpecLate.lean; tokens: Rom/Defer.lean; words of this
library: lean/GLOSSARY.md).
This file does not prove the game hop (`hopLateBP`, Compile/Batch/PubLate.lean).

  `RelB`            (1) equal private states (s = s'); (2) no token ≥ n has a closure in Γ
                    (`Fut n Γ`); (3) after the setup (s = some (k, N₀)): N₀ ≤ n, the tokens at the
                    salted leaves of the copies' trees are below N₀, and Γ knows the symbols under
                    them (exactly: `IskK`, Compile/Batch/SpecLate.lean: for the salt Γ records no
                    closure that holds data but, at most, the one with the true symbol; for the
                    digest none that holds data)

Notation:
  `n`: a natural number; in `Rom.Late` (Rom/DeferLate.lean) a lower bound on the number of tokens
    that exist;
  `Γ`: a `Cx lam W.K L` (Compile/Batch/Mirror.lean), that is a `Ctx` (Rom/DeferLate.lean): which
    closure the `Step` program gave when it charged token t at oracle o;
  closure: a `Clo S o` (Rom/DeferLate.lean): how the point of a marked evaluation of o is made of
    the value of the charged token and the values of the others;
  `s`, `s'`: the private states (in `late_stepBP`, Compile/Batch/PubLate.lean: of `VCBP`, of
    `chalLBP`), of type `Option (IskH lam L × ℕ)`; `k`: an `IskH lam L` (Compile/Batch/Star.lean);
    `N₀`: a natural number;
  `LStep` (Rom/DeferLate.lean): one step of a challenger that supplies points at the release; as
    `Step`, but for marked and reveal;
  mode I (the head of Rom/Defer.lean): a marked evaluation returns a fresh uniform answer and does
    not touch the table; its release writes it there, if the entry is still empty.
-/
import Compile.Batch.ChallL
import Compile.Batch.SpecLate
import Iop.BatchFmt
import Rom.DeferLateProof
import Compile.Batch.RealB
import Compile.Step1_life2_Chall

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall GAdm)
open Compile.Life2 (virt up)
open Compile.DefC (virtL late_virt)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the relation between the private states, with what the context Γ knows -/
def RelB (W : QueryLayout lam L) (n : ℕ) (Γ : Cx lam W.K L) (s s' : Option (IskH lam L × ℕ)) : Prop :=
  s = s' ∧ Fut n Γ ∧ match s with
    | none => True
    | some (k, N₀) => N₀ ≤ n ∧ IskK Γ N₀ k

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)



end Compile.Batch
