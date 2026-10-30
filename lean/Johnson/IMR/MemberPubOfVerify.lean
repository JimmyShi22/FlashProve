-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberPubOfVerify.lean: FROM verify()'s ACCEPT ALONE TO THE MEMBERS
OF "REACHED" ON EACH OF THE THREE CHAINS, IN ONE THEOREM: IM.member_pub (Johnson/IMR/MemberPub.lean)
composed
with IM.gate_of_verify (Johnson/IMR/MemberOfVerify.lean), with "the public files are in the goals'
scope" in
its end, since every law of this folder in scope takes that as a premise.

  pub_of_verify    wherever the goals' verifier at the named description accepts (at any parser
                   argument, form and hash function): InScope Z = true, and there are z, v₁ with
                   member_pub's whole conclusion at P := Z.
  verdict_in_scope   the ride's own verdict "some true" gives InScope Z = true.

THE WORDING THAT TRAVELS WITH EVERY USE: whatever is met through this
file is "met at an accepting run at these public files", NOT "at the honest run": z and the views
are had by contradiction: they are tied neither to the prompt, the reply, the commitment ID or the
form, nor to the hash function.
WHAT IS NOT SAID. That verify() accepts anywhere: a run's to show. "No mark", or anything else, of
the shared or the second chain's states. All that Johnson/IMR/MemberPub.lean and
Johnson/IMR/MemberOfVerify.lean do
not say. No soundness.
-/
import Johnson.IMR.MemberPub
import Johnson.IMR.MemberOfVerdict

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (RchPub RchPub₂ RchPub₃)
open VerifierAndGoals FlashProve

/-- **From verify()'s accept alone: in scope, and the members of "reached" on each chain**, at some
instance and views. -/
theorem pub_of_verify (Z : VerifierAndGoals.PublicFiles) {Form : Type}
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (hash : VerifiableInference.Hash)
    (commitment : VerifiableInference.Commitment)
    (prompt output : List VerifiableInference.Token) (form : Form)
    (h : (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
      hash = true) :
    VerifierAndGoals.InScope Z = true ∧
    ∃ (z : LPFD.Full.XF × OnBytes.Flat.RecFull) (v₁ : Fmt.View) (pp : Inst.Model.ScalesAndPolicy)
      (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl)) (c : Chain S Cl)
      (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (st : ℕ → S)
      (st₂ : ℕ → (fileOf Zp A B c).S₂) (st₃ : ℕ → (fileOf Zp A B c).S₃),
      VerifierAndGoals.readFiles Z = .ok pp ∧
      Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (fileOf Zp A B c) Zp Bs base c A B ∧
      RunAt Zp c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st ∧
      (∀ k ≤ 358, ∀ (Str : Type) (y : Str),
        RchPub (fileOf Zp A B c) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          (((LPFD.Full.instanceAsPlainRecord z).pub, st k), y)) ∧
      (∀ k ≤ (fileOf Zp A B c).shared.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₂ (fileOf Zp A B c) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358), st₂ k), y)) ∧
      ∀ k ≤ (fileOf Zp A B c).second.blocksInOrder.length, ∀ (Str : Type) (y : Str),
        RchPub₃ (fileOf Zp A B c) (fun p => ∃ z', p = (LPFD.Full.instanceAsPlainRecord z').pub) k
          ((((LPFD.Full.instanceAsPlainRecord z).pub, st 358, st₂ (fileOf Zp A B c).shared.blocksInOrder.length),
            st₃ k), y) := by
  obtain ⟨hS, z, v₁, v₂, v₃, hg⟩ := gate_of_verify Z parse hash commitment prompt output form h
  exact ⟨hS, z, v₁, member_pub hS hg⟩

/-- The ride's own verdict "some true" gives the scope. -/
theorem verdict_in_scope (ℓ : PV.Ride.Lets) (Z : VerifierAndGoals.PublicFiles) (sh : PV.Ride.Shares ℓ flashProveData Z)
    (O : ByteArray → ByteArray) (B : FlashProve.FormBytes)
    (commitment : VerifiableInference.Commitment)
    (prompt output : List VerifiableInference.Token)
    (h : PV.Ride.verdictThe Z O B (PV.Ride.rideOf ℓ Z O B commitment prompt output) = some true) :
    VerifierAndGoals.InScope Z = true :=
  (gate_of_verify Z _ _ commitment prompt output B
    (PV.Ride.verdictThe_of_shares ℓ Z sh O B commitment prompt output true h).symm).1

#print axioms pub_of_verify
#print axioms verdict_in_scope

end IM
