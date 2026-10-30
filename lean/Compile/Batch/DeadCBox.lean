-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DeadCBox.lean: under `W.OKG`, if σ.o = other, the committer of `argP` depends on its
oracle answers only up to `agF W` (words of this library: lean/GLOSSARY.md).

Compile/Batch/DeadC.lean takes two facts on `proveB` as hypotheses (`BoxT`, `BoxL`). Here they
follow from `lw_proveB` (Compile/Batch/DeadProver.lean), at the lists of trees [tree] and [root,
tree] and the one slot [some ()]:

  `boxT_of`, `boxL_of`  For every relation ag that relates nothing but at the Fiat-Shamir oracles
                        `fb t` and their ghost names `fbw t j`, and says at the searches of Test, of
                        Link, what `FitsSh` requires.
  `facF_C_argP_of`  ∀ i, ((argP W WP p bk σ).C i).FactorsBy (agF W), from σ.o = other and
                    `FitsSh (agF W)` for Test and for Link. (`FitsSh`: two answers that agF W
                    relates at the query of an attempt both fail that search's own check, and the
                    attempt is not the last; where a round has no proof-of-work bits, agF W relates
                    nothing at its query.)
  `facF_C`  The same from `W.OKG` and σ.o = other: `FitsSh (agF W)` holds for every well-formed wire
            record (`fitsSh_agF`, Compile/Batch/DeadFits.lean).

Limits: nothing on P or V; nothing on the schemes above `argP`; nothing on numbers of queries.
-/
import Compile.Batch.DeadC
import Compile.Batch.DeadProver
import Compile.Batch.DeadFits

noncomputable section

namespace Compile.Batch.Dead
open Iop Rom Compile

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem boxT_of (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hag : OnlyFb ag)
    (hF : FitsSh ag .test (BatchInteractiveOracleProof.ofProto L.offline).loc.shape
      (BatchInteractiveOracleProof.ofProto L.offline).ann W.T.sh id) : BoxT W WP p ag :=
  fun _ _ _ _ h => lw_proveB hag _ _ _ _ _ _ _ _ _ _ _ _ _ hF (fun tr htr u hu => by
    obtain rfl := List.mem_singleton.1 htr
    exact h u hu) _ _ (.inl (List.cons_ne_nil _ _))

theorem boxL_of (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
    {ag : ∀ o, domOf lam L o → rngOf lam W.K o → rngOf lam W.K o → Prop} (hag : OnlyFb ag)
    (hF : FitsSh ag .link (BatchInteractiveOracleProof.ofProto L.link).loc.shape
      (BatchInteractiveOracleProof.ofProto L.link).ann W.Lk.sh id) : BoxL W WP p ag :=
  fun _ _ _ _ _ _ h₀ h => lw_proveB hag _ _ _ _ _ _ _ _ _ _ _ _ _ hF (fun tr htr u hu => by
    rcases List.mem_cons.1 htr with e | e
    · subst e
      exact h₀ u hu
    · obtain rfl := List.mem_singleton.1 e
      exact h u hu) _ _ (.inl (List.cons_ne_nil _ _))

/-- If σ.o = other: the committer of argP has `FactorsBy (agF W)`, from what agF W says at the
searches of Test and of Link. -/
theorem facF_C_argP_of (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other)
    (hFT : FitsSh (agF W) .test (BatchInteractiveOracleProof.ofProto L.offline).loc.shape
      (BatchInteractiveOracleProof.ofProto L.offline).ann W.T.sh id)
    (hFL : FitsSh (agF W) .link (BatchInteractiveOracleProof.ofProto L.link).loc.shape
      (BatchInteractiveOracleProof.ofProto L.link).ann W.Lk.sh id) (i : I) :
    ((argP W WP p bk σ).C i).FactorsBy (agF W) :=
  facF_C_argP W WP p bk σ hσ (boxT_of W WP p (onlyFb_agF W) hFT)
    (boxL_of W WP p (onlyFb_agF W) hFL) i

/-- Under `W.OKG`, if σ.o = other: the committer of argP has `FactorsBy (agF W)`. -/
theorem facF_C (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (hW : W.OKG) (hσ : σ.o = OracleName.other) (i : I) :
    ((argP W WP p bk σ).C i).FactorsBy (agF W) :=
  facF_C_argP_of W WP p bk σ hσ (fitsSh_agF W .test _ _ _ id hW.T.sh fun _ => rfl)
    (fitsSh_agF W .link _ _ _ id hW.Lk.sh fun _ => rfl) i

end Compile.Batch.Dead
