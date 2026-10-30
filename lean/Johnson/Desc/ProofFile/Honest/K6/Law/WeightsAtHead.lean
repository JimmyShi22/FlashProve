-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/WeightsAtHead.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE FACTS ON
THE PUBLIC PARAMETERS' LAYOUT OF THE COMMITTED WEIGHTS (Cells/TensorLaid.lean: WeightsLaid: three
fields, five clauses) HOLD AT THE LIBRARY'S HEAD.
WHAT IT IS NOT. CONDITIONAL on the library's hypothesis h, of which three fields are spent: the
public files are in the goals' scope, they are read, and the public parameters are what the
verifier's own function returns on them. On public data alone: no prover, no state, no weight's
value. A joining: two calls. Nothing on soundness, on completeness or on what a proof hides.
OF THE FOLDER Johnson/Goal/: this file imports Johnson/Goal/Meaning/EmbScope.lean directly and calls
its emb_public_in_scope; nothing else of that folder is named.
CALLED: Meaning.Emb.emb_public_in_scope (its second and third conjuncts are the fields sized and
laid), last_unit (Law/FitsOf.lean: the field unit, without its clause on the digits).

-/
import Johnson.Desc.ProofFile.Honest.K6.Cells.TensorLaid
import Johnson.Desc.ProofFile.Honest.K6.Law.FitsOf
import Johnson.Goal.Meaning.EmbScope
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WeightsLaid AT THE LIBRARY'S HEAD.** CONDITIONAL on the one hypothesis. -/
theorem weightsLaid_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    WeightsLaid (P5J.At.X Zp) := by
  obtain ⟨-, hs, hl, -⟩ := Meaning.Emb.emb_public_in_scope h.scope h.reads h.pubOne
  obtain ⟨u, hu, h13, -, hg⟩ := last_unit h.pubOne
  exact ⟨hs, hl, u, hu, h13, hg⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.weightsLaid_at_head
