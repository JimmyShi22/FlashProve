-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/Kinds/Law/HeadCutsOfPin.lean: THE FIELD head_cuts AT THE COMPOSED MEANING's CONSTANT
FROM THE CONSTANT's HEAD AND ONE PUBLIC TEST (madePinnedAt). Three theorems, each
a few calls.

  laidPOf_of_laidAt  what "laid" holds at the term's letters (P5J/LaidOpens.lean: LaidAt) gives back
                     "the proof file's value is laid": by the converse that lies beside laidPOf_ok
                     (Johnson/Desc/Laid/ProofFullLaw.lean: laidPOf_of).
  tests_of_pin       under the head (P5J/AtMg.lean) and that test's accept, the two cheap public
                     tests planK6AtZ and padsAtZ accept: Goal/Meaning/HeadTestsScope.lean's
                     tests_at_older, five of its six premises had from the head's fields.
  headCuts_of_pin    Law/HeadCutsOfPads.lean's headCuts_of_pads with its premise padsAtZ so paid.

WHAT IT IS NOT. Implications. THE HEAD h IS A PREMISE: a member of the head is proved at storedPublicFiles and
zGap alone (at secondHashFunction; side library AtFullSide/Top/). THAT
TEST STAYS A PREMISE: that a verifier asks it is not said here. The second hash function o is a
letter. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Johnson.Desc.Kinds.Law.HeadCutsOfPads
import Johnson.Goal.Meaning.HeadTestsScope
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA LaidAt TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **What "laid" holds gives "laid" back.** -/
theorem laidPOf_of_laidAt {pol lay KL : ByteArray} (L : LaidAt o pol lay KL D r Zp Np cF) :
    LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r) := by
  rw [L.run]
  exact LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks

/-- **Under the head and the one test, the two cheap public tests accept.** -/
theorem tests_of_pin (h : AtMg o Z D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    OffPad.planK6AtZ Zp = true ∧ OffPad.padsAtZ Zp = true :=
  OffPad.tests_at_older h.scope h.reads h.laid.pub hy (laidPOf_of_laidAt h.laid) h.pubOne

/-- **"HEAD CUTS" AT THE CONSTANT, FROM ITS HEAD AND THE ONE TEST.** -/
theorem headCuts_of_pin {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA o Z D r Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    P5J.HeadCuts (VerifiableInference.OnPublicFiles.ppAtFiles Z.pol Z.KL) OnBytes.Flat.putReq h.𝔇.H
      h.𝔇.headPart :=
  headCuts_of_pads h (tests_of_pin h.toAtMg hy).2

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.laidPOf_of_laidAt
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tests_of_pin
#print axioms VerifiableInference.Desc.Kinds.Head.Law.headCuts_of_pin
