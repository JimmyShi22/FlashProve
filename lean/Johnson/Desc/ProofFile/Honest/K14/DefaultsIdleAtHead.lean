-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/DefaultsIdleAtHead.lean: kind K14: at the full size, at the shared
chain's own plan, the sentences on the silent cases (1) to (9) of the list in
Honest/K14/DefaultsIdle.lean hold. One statement: calls.

  publicIdle_at_head   PublicIdle (qAt Zp Np)

That qAt Zp Np is the plan which the fillings' maker of the six halves reads at that public part:
filling_at_head (Honest/K14/SendingsAtFilling.lean).

Limits. THE PREMISE h IS A HYPOTHESIS: P5J.AtMgA (Johnson/P5J/MgAtAll.lean) gathers conditions on
the public files at the full size. This file does not show them to be met, and by that file's head
the verifier does not ask them; a member is proved at two written sets of public files
(AtFullSide/Top/: headMember_zFull, headMember_zGap), and at no others. The limits of
Honest/K14/DefaultsIdle.lean hold here too.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.DefaultsIdle
import Johnson.Desc.ProofFile.Honest.K14.SendingsAtFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)

/-- **At the full size, at the shared chain's own plan, the sentences on the cases (1) to (9)
hold.** -/
theorem publicIdle_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀) : PublicIdle (qAt Zp Np) :=
  publicIdle_of_fit (sendings_at_head h).1 (sendings_at_head h).2.2.2.2.1
    (sendings_at_head h).2.2.2.2.2 (sendings_at_head h).2.1 (linOk_at_head h)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.publicIdle_at_head
