-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/ShutRestAt.lean: TWO SMALL SENTENCES OF THE SHUTTING's
SIDE OF K9's CONDITION (Link/Law/ShutRest.lean · P5J/K09Rest.lean) AT THE
CLOSED CONSTANT. THE REST OF THAT SIDE LIES ALREADY, IN OTHER FILES, AND IS NOT TYPED AGAIN HERE.

  pub_at           ∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zp: LaidAt's field pub
                   (pureRoad.pub is pubPlain by definition)
  carry_at         THE FIELD hcr AT layF := Z.lay: h.𝔇.cr1 = carryAtZ Zp Z.lay: by definition

WHAT LIES ELSEWHERE (found by searching and by report): hW AND hbase, at Dw := D:
P1L20.whole_atAll (Johnson/P1L20R/FrameFourAll.lean) · "the place
whose switch opens group 25 does not stand in the head's dress": stands24 (Johnson/Top/H0/
K2Caller/Stands24.lean), under the named test spotsFitB Zp and "25 links" · mh: K9RestLight.lean.


Limits. No law of any sub-protocol. No soundness statement.

-/
import Johnson.P5J.MgAtAll
import Johnson.P1L20R.FrameAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.K2Caller (carryAtZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- The public part is the pure road's. -/
theorem pub_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zp :=
  ⟨_, _, _, _, h.toAtMg.laid.pub⟩

/-- **ShutRest's FIELD hcr, AT layF := Z.lay.** -/
theorem carry_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    h.𝔇.cr1 = carryAtZ Zp Z.lay := rfl

end P5J

#print axioms P5J.pub_at
#print axioms P5J.carry_at
