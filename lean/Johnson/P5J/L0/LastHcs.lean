-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastHcs.lean: **THE TWO PATHS TO THE CODES ARE ONE UNDER THE HEAD**: the first table's
constant's `At.cs Zp` (Zp.made.p.chains.proof.first.codes) is the two later tables' `(p14At Zp).codes`
(Zp.p.chains.made.sized.proof.codes), at every head `AtMg …`: ONE CALL of
`Desc.K14.Law.Sh.hcs_of_read` (Johnson/Desc/AtSeats/ShCodesOfRead.lean), from two fields of "laid":
the public files' reading, and the description's own test on the plan. No pin, no scope.
Limits. One call. Nothing on soundness, nothing on hiding.
-/
import Johnson.P5J.FourAtMg
import Johnson.Desc.AtSeats.ShCodesOfRead
import Johnson.ToldDescR.LastBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Chain)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **hcs, under the head.** -/
theorem AtMg.hcs (h : AtMg o Z D r Zp Np cF) : At.cs Zp = (ToldDesc.p14At Zp).codes :=
  _root_.Desc.K14.Law.Sh.hcs_of_read h.laid.pub Np (_root_.Desc.K14.Law.secondAt Zp Np) cF
    h.laid.planOk (F0T o Zp Np cF)

end P5J

#print axioms P5J.AtMg.hcs
