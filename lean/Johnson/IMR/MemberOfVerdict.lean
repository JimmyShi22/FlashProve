-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberOfVerdict.lean: FROM THE RIDE's PRINTED VERDICT TO AN OPENING
AND A RUN, BY THEOREMS ALL THE WAY: a better road than
Johnson/IMR/MemberOfRide.lean's: the verdict "some true" OF THE RIDE ITSELF (not
of a free letter) is the goals' verifier's accept (the tie PV.Ride.verdictThe_of_shares,
Johnson/PVR/RideThe.lean), and an accept gives the member (IM.member_of_verify).

  member_of_verdict   at every structure of letters that shares the named description's eight at
                   these public files: verdictThe Z O B (rideOf ℓ Z O B commitment prompt output) =
                   some true gives z, v₁, an opening and a run. (At the ride's own letters: sh :=
                   PV.Ride.shares_the Z; at the telling ones: PV.Ride.shares_tell Z.)

THE LIMIT IS Johnson/IMR/MemberOfVerify.lean's, AND IT COSTS MORE THAN "SOME INSTANCE" SOUNDS (the
same reader): the conclusion reads the public files alone: z and the views are tied NEITHER to the
prompt, the reply, the commitment ID or the form, NOR TO THE HASH FUNCTION. So what may be written
of a premise that is met through this file is "met at an accepting run at these public files", NOT
"at the honest run".
WHAT STAYS BY READING: that the harness prints "VERDICT yes" just where this term is some true; that
compiled code computes what the terms mean; that the compiled files which ran are these sources'.
WHAT IS NOT SAID. That any ride printed anything. No soundness.
-/
import Johnson.IMR.MemberOfVerify
import Johnson.PVR.RideThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open VerifierAndGoals FlashProve

/-- **From the ride's verdict to an opening and a run**, at some instance and views. -/
theorem member_of_verdict (ℓ : PV.Ride.Lets) (Z : VerifierAndGoals.PublicFiles) (sh : PV.Ride.Shares ℓ flashProveData Z)
    (O : ByteArray → ByteArray) (B : FlashProve.FormBytes)
    (commitment : VerifiableInference.Commitment) (prompt output : List VerifiableInference.Token)
    (h : PV.Ride.verdictThe Z O B (PV.Ride.rideOf ℓ Z O B commitment prompt output) = some true) :
    ∃ (z : LPFD.Full.XF × OnBytes.Flat.RecFull) (v₁ : Fmt.View) (pp : Inst.Model.ScalesAndPolicy)
      (F : FileDescription ProofFile.Inst) (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat) (st : ℕ → S),
      VerifierAndGoals.readFiles Z = .ok pp ∧
      Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B' ∧
      RunAt Zp c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st :=
  member_of_verify Z _ _ commitment prompt output B
    (PV.Ride.verdictThe_of_shares ℓ Z sh O B commitment prompt output true h).symm

#print axioms member_of_verdict

end IM
