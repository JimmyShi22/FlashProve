-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/One.lean: from typed oracles to one hash function, for index binding of a
scheme with the verifier `VC` (Cms.lean of this folder).

After lean/Johnson/RecCompile/One.lean, in that file's words. The extractor `extractorC0` reads its
trace through Merkle entries alone (`LocalTo`, Rom/Family.lean), so the library's passage
(`Rom.binding_overOne`, Rom/ExitBind.lean) takes it, with the same bound; budgets then count queries
to the one hash function.

Limits: for a query encoding m whose leaf and node answers are one hash block. That such an m exists
at this carrier is not shown here.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsGlue
import OnBytes.TypedOracleCompiler.Compile.Batch.Local
import Rom.ExitBind

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits
                              L.link.shape}

theorem extractorC0_local (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L
                                         Bd aT aL)) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) : LocalTo (extractorC0 W) m :=
  ⟨fun v tr => by
    show L.decodeIndex (extEnc W tr v.cm) v.rcd = L.decodeIndex (extEnc W (single m tr) v.cm) v.rcd
    rw [extEnc_single W m hl hn], fun _ _ _ _ _ => rfl⟩

/-- Index binding over one hash function, same bound. -/
theorem binding_one {ISK PP : Type} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (R : ZKCP.Gen.RelPair I X Unit PP)
    (A : ZKCP.Gen.Arg (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) I X Unit (FullKey lam L aT aL) ISK (RequestProof lam
                                  L))
    (ε : ℕ → ℕ → ℝ≥0∞) (h : ZKCP.Gen.HasIndexBindingWith R A (extractorC0 W) ε) :
    ZKCP.Gen.HasIndexBindingWith R (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (extractorC0 W)) ε :=
  binding_overOne m R A (extractorC0 W) (extractorC0_local W m hl hn) ε h

end TypedOracleCompiler.Compile.Batch.Cms
