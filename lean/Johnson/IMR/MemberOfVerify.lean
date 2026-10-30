-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberOfVerify.lean: FROM verify()'s ACCEPT ALONE TO AN OPENING AND
A RUN: wherever the goals' verifier at the named description accepts (at any parser argument, form
and hash function), the two premises of IM's member theorems hold at some instance and views: so
every member at "reached" hangs on ONE Bool, the verifier's accept, BY A THEOREM.

  gate_of_verify   an accept gives: the public files are in the goals' scope, and there are z, v₁,
                   v₂, v₃ at which the proof file's decision behind its gate accepts. (Two calls:
                   FlashProve.scope_of_accept and FlashProve.gates_of_accept:
                   Johnson/Goal/Description/AcceptGivesLive.lean and
                   AcceptGivesGates.lean.)
  member_of_verify   so: z, v₁, v₂, v₃, an opening and a run (IM.at_gate's conclusion).

THE LIMIT, WHICH WHOEVER SPENDS THIS MUST WEIGH. "THERE ARE z, v₁, v₂, v₃": BY CONTRADICTION (the
called law's own head: "no instance and no views are named: they need not be those that a run's fast
form hands the decision"). SO THE RUN HERE IS A RUN AT SOME INSTANCE: IT IS NOT SAID TO BE AT THIS
prompt AND output, NOR AT THE VIEWS OF THIS form. For "the premises can be met" that is enough. For
a fact on THIS request's run it is not: there MemberOfRide.lean's telling line, or a law that
names the views, is wanted.
WHAT IS NOT SAID. That verify() accepts anywhere: a run's to show. All that
Johnson/IMR/MemberFold.lean and
Johnson/IMR/MemberThree.lean do not say. No soundness.
-/
import Johnson.IMR.MemberRun
import Johnson.Goal.Description.AcceptGivesGates

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)
open VerifierAndGoals FlashProve

section
variable (Z : VerifierAndGoals.PublicFiles) {Form : Type} (parse : Parser (atSecondHashFunction theDescription) Z Form)
  (hash : VerifiableInference.Hash) (commitment : VerifiableInference.Commitment)
  (prompt output : List VerifiableInference.Token) (form : Form)
  (h : (VerifierAndGoals.verify (atSecondHashFunction theDescription) Z parse commitment prompt output form).evaluate
    hash = true)
include h

/-- **An accept gives the two premises of IM's member theorems**, at some instance and views. -/
theorem gate_of_verify :
    VerifierAndGoals.InScope Z = true ∧
      ∃ z v₁ v₂ v₃, FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles Z) z v₁ v₂ v₃ = true :=
  ⟨scope_of_accept _ Z parse hash commitment prompt output form h,
    (gates_of_accept Z parse hash commitment prompt output form h).2.2⟩

/-- **From verify()'s accept alone: an opening and a run**, at some instance and views. -/
theorem member_of_verify :
    ∃ (z : LPFD.Full.XF × OnBytes.Flat.RecFull) (v₁ : Fmt.View) (pp : Inst.Model.ScalesAndPolicy)
      (F : FileDescription ProofFile.Inst) (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block S Cl))
      (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (st : ℕ → S),
      VerifierAndGoals.readFiles Z = .ok pp ∧
      Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B ∧
      RunAt Zp c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st := by
  obtain ⟨hS, z, v₁, v₂, v₃, hg⟩ := gate_of_verify Z parse hash commitment prompt output form h
  exact ⟨z, v₁, at_gate hS hg⟩

end

#print axioms gate_of_verify
#print axioms member_of_verify

end IM
