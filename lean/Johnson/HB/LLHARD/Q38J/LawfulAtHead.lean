-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/HB/LLHARD/Q38J/LawfulAtHead.lean: under the head, the request's layout has passed the
programs' own test on a layout, at the closed letters.

What is shown.
  `lawful_at_head`: **`reqLayoutOk (At.cs Zp) (At.shape Zp) (At.layout Zp) = true`.** A call of
    `pub_layoutOk` (Johnson/IMR/LayoutOkPub.lean) at the head's own field: the public part is made.

Grade. From the head alone: no entry test and no fact on reached states is spent.

Limits. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). Nothing on soundness.


-/
import Johnson.P5J.MgAtAll
import Johnson.IMR.LayoutOkPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The layout is lawful.** -/
theorem lawful_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) = true :=
  Meaning.K2.pub_layoutOk
    (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp from h.laid.pub)

end Q38

#print axioms Q38.lawful_at_head
