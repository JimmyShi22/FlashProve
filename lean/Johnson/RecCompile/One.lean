-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/One.lean: FROM TYPED ORACLES TO ONE HASH FUNCTION, for index binding of a scheme
with the verifier VC (Cms.lean): the extractor extractorC0 reads its trace through Merkle entries
alone (LocalTo, Rom/Family.lean), so the library's passage (Rom.binding_overOne, Rom/ExitBind.lean)
takes it, with the same bound; budgets then count queries to the one hash function.
For a query encoding m : OracleCoding (spec ..) lam whose leaf and node answers are one hash block. That
such an m exists at the carrier is not shown here (the library's like: CompileK/ImplExists.lean,
ImplCountable.lean).

-/
import Johnson.RecCompile.CmsGlue
import Compile.Batch.Local
import Rom.ExitBind

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X}

theorem extractorC0_local (W : QueryLayout lam L.carrierC) (m : OracleCoding (spec lam W.K L.carrierC) lam)
    (hl : m.blocks OracleName.leaf = 1) (hn : m.blocks OracleName.node = 1) : LocalTo (extractorC0 W) m :=
  ⟨fun v tr => by
    show L.decodeIndex (extEnc W tr v.cm) v.rcd = L.decodeIndex (extEnc W (single m tr) v.cm) v.rcd
    rw [extEnc_single W m hl hn], fun _ _ _ _ _ => rfl⟩

/-- Index binding over one hash function, same bound. -/
theorem binding_one {ISK PP : Type} (W : QueryLayout lam L.carrierC)
    (m : OracleCoding (spec lam W.K L.carrierC) lam) (hl : m.blocks OracleName.leaf = 1)
    (hn : m.blocks OracleName.node = 1) (R : ZKCP.Gen.RelPair I X Unit PP)
    (A : ZKCP.Gen.Arg (spec lam W.K L.carrierC) I X Unit (FullKey lam L) ISK (RequestProof lam L))
    (ε : ℕ → ℕ → ℝ≥0∞) (h : ZKCP.Gen.HasIndexBindingWith R A (extractorC0 W) ε) :
    ZKCP.Gen.HasIndexBindingWith R (schemeOverOneHashFunction m A) (extractorOverOneHashFunction m (extractorC0 W)) ε :=
  binding_overOne m R A (extractorC0 W) (extractorC0_local W m hl hn) ε h

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.binding_one
