-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReqOkOfStart.lean: AT THE PROOF FILE's OWN DESCRIPTION (`P5J.F0T`,
Johnson/P5J/AtTerm.lean): WHERE THE DESCRIPTION's TESTS ON THE INSTANCE SAY YES, THE REQUEST PASSES
THE FIRST STATE's OWN TEST. One law; over the library alone; nothing is evaluated.

Main name.
* `reqOk_of_okStart`: (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true gives (Zp.s₀.withReq
  (Verify.words32 ξ.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true. The description's field
  okStart is two tests joined (`ProofFile.fileDescBy`, Johnson/Desc/ProofFile/Frames1.lean); the first
  gives it by `Meaning.K2.okBy_reqOk` (Johnson/IMR/RecRun.lean).

What it is for. Laws on the first chain's start ask that the request passes that test; a rule on the
whole file has the description's tests on the instance among its premises.

Limits. An implication: that the tests on the instance say yes at any instance is not shown. At the
format's second hash function. Nothing on soundness, completeness or hiding.
-/
import Johnson.IMR.RecRun
import Johnson.P5J.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open P5J (F0T)

/-- Where the file's tests on the instance say yes, the request passes the state's own test. -/
theorem reqOk_of_okStart {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    (Zp.s₀.withReq (Verify.words32 ξ.pub.request)).reqOk Zp.p.X.T Zp.p.X.P.h.V = true := by
  have h' : (ProofFile.okBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp ξ && _) = true := hx
  rw [Bool.and_eq_true] at h'
  exact Meaning.K2.okBy_reqOk h'.1

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.reqOk_of_okStart
