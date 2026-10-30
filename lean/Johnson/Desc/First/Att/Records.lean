-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Records.lean: the four records that OnBytes/Model's verifier fills in an attention
segment's own rounds, as one record. A seat's tool; no part of the kind.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Model.AttentionScores
import OnBytes.Model.AttentionDivide

namespace VerifiableInference.Desc.First.Att
open OnBytes.Attention

/-- What the routines of OnBytes/Model's verifier for these rounds return. -/
structure Own where
  planes : Array PlaneClaim
  scores : Array Score
  d : Divide
  x : Attain

end VerifiableInference.Desc.First.Att
