--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/L0/LastMq.lean: THE FIRST TABLE's MEANING AS THE TOWER SPELLS IT AT THE CLOSED CONSTANT,
`h.toAtMg.mq h.𝔇`, IS THE COMPOSED MEANING `mgAll h.𝔇 mgBase`: another house's two lemmas (`mgAt_is_mq`,
Johnson/P5J/RowsAtMg.lean; `mgAtAll_is`, Johnson/P5J/MgAtAll.lean), joined. FOR WHOEVER PAYS A PREMISE OF THE LAST
TABLE's LAW AT `mgAll …` and must end at the tower's spelling: one rewrite.
Limits. One equation. Nothing on soundness, nothing on hiding.
-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (mgAll mgBase)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The tower's spelling of the first table's meaning is the composed meaning.** -/
theorem AtMgA.mq_is (h : AtMgA o Z D r Zp Np cF x) : h.toAtMg.mq h.𝔇 = mgAll h.𝔇 mgBase :=
  (mgAt_is_mq h.toAtMg h.𝔇).symm.trans (mgAtAll_is h).symm

end P5J

#print axioms P5J.AtMgA.mq_is
