-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Top/ProgN.lean: of an answer of the auxiliary oracle (`OracleName.other`, Compile/Batch/Oracles.lean)
  every block is needed. (Terms: lean/GLOSSARY.md.)
    `whole_of_eq`   At the auxiliary oracle two answers that agree on what is needed (`agree nb`,
                    Compile/Batch/NeedTable.lean) are equal.
  It has the form of the hypothesis on the derivation oracle of `facOK_argPL`
  (Compile/Batch/NeedL.lean; `facOK_argP` of Compile/Batch/NeedP.lean asks the same), for a seed
  oracle σ that reads the auxiliary oracle (σ.o = OracleName.other). No file of this library applies it.
  Notation: the auxiliary oracle, `OracleName.other`: the oracle on bit strings; block: an answer of a typed
  oracle is a tuple of hash blocks of lam bits (Rom/OverOneN.lean); needed: the blocks that `need`
  marks: all, except at a Fiat-Shamir query (Compile/Batch/NeedTable.lean).
  Limits: Nothing on a scheme.
-/
import Top.Prog
import Compile.Batch.NeedP
import Compile.Batch.NeedL
import Compile.BindingManyExit

noncomputable section

namespace Top.Prog
open Iop Rom ZKCP Compile Compile.Batch
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- At the auxiliary oracle two answers that agree on what is needed are equal. -/
theorem whole_of_eq {K : ℕ} (nb : Tag → ℕ → ℕ)
    {o : Compile.Batch.OracleName} (h : o = Compile.Batch.OracleName.other) :
    ∀ (q : domOf lam L o) (r r' : rngOf lam K o), Need.agree nb o q r r' → r = r' := by
  subst h
  exact fun _ _ _ e => e

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
  (σ : SeedOracle (Compile.Batch.spec lam W.K L))
  (m : OracleCoding (Compile.Batch.spec lam W.K L) lam) (nb : Tag → ℕ → ℕ)



variable {W WP p bk σ m nb} (hW : W.NB nb) (hσ : σ.o = Compile.Batch.OracleName.other) (hm : Need.Std m)
include hW hσ hm


variable {PP : Type} (R : Gen.RelPair I X Unit PP)





end Top.Prog
