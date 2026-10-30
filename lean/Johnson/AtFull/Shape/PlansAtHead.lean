-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/PlansAtHead.lean: under the head at which the library's laws on the proof
file's own first chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): every member of the chain's flat
list passes its own test on the plan. One law, read off the head's field "the description passes its
tests on the plan". Nothing is evaluated.

  **`plans_at`**: ∀ b ∈ cF.blocksInOrder, b.planOk = true.

Limits. That the head has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files, in a side library. At the format's second hash function (OnBytes.secondHashFunction). Nothing on
soundness, completeness or hiding.
-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head every member of the chain's flat list passes its own test on the plan.** -/
theorem plans_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : ∀ b ∈ cF.blocksInOrder, b.planOk = true :=
  fun b hb => ((((F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1 h.laid.planOk).blocks₁ b hb).1

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.plans_at
