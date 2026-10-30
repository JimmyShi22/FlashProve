-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MemberOfRide.lean (no file of this library imports it): FROM WHAT THE REFERENCE RIDE
PRINTS, IN THE
RIDE's OWN LETTERS, TO THE TWO PREMISES OF THE MEMBER THEOREMS: to shut two of
the gaps between a print and "InScope P = true and theProofGate (asDescriptionFiles P) z v₁ v₂ v₃ = true".

  scope_of_verdict   where the ride's verdict (PV.Ride.verdictThe) is "some true": the public files
                   are in the goals' scope, the live test passes, and the ride returned steps that
                   all say yes. SO THE SCOPE NEED NOT BE READ OFF THE LABEL OF A ROW: the printed
                   verdict has it, by a theorem.
  tell_is_gate     the telling letters' decision for the proof file, at asDescriptionFiles Z, IS
                   FlashProve.theProofGate (asDescriptionFiles Z): by rfl.
  member_of_ride   from "the verdict is some true" and "the telling decision returned true at z, v₁,
                   v₂, v₃": an opening and a run (IM.at_gate's conclusion) at P := Z.

WHAT STAYS BY READING, AND OF WHICH TEXTS. (1) That the line "VERDICT yes" is printed just where
verdictThe … = some true: the harness's text. (2) That the line "DECISION|the proof file's
(theProofGate)|reached|it answers yes" is printed by PV.Ride.tell3 at a call d a u v w whose value
is true: tell3's text: it prints "yes" just if d a u v w, and returns d a u v w. (3) That the ride
hands the telling decision asDescriptionFiles Z OF THE SAME Z: PV.Ride.rideOf's text: every letter is taken at
asDescriptionFiles Z. (4) That compiled code computes what the terms mean. (5) That the compiled files which
ran are these sources'. The arguments z, v₁, v₂, v₃ of the call are not printed: existence is all
that the member theorems need.
WHAT IS NOT SAID. That any ride printed anything. That a verdict "some true" by itself gives the
gate's accepting at some z, v₁, v₂, v₃: THE ARM THAT CALLS THE DECISION IS A COMPILED VERIFIER's,
AND NO LAW HERE OPENS IT: so the second premise is taken from the telling line, not from the
verdict. No soundness.
-/
import Johnson.IMR.MemberRun
import Johnson.PVR.RideThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- **Where the ride's verdict is "some true"**: in scope, live, and the ride returned steps that
all say yes. -/
theorem scope_of_verdict {Z : VerifierAndGoals.PublicFiles} {O : ByteArray → ByteArray} {B : FlashProve.FormBytes}
    {r : Except String VerifiableInference.OnPublicFiles.SlotsBehindCutD.FastSteps}
    (h : PV.Ride.verdictThe Z O B r = some true) :
    VerifierAndGoals.InScope Z = true ∧ FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true ∧
      ∃ s, r = .ok s ∧ s.yes = true := by
  unfold PV.Ride.verdictThe at h
  split at h
  · split at h <;> cases h
  · rename_i hn
    unfold PV.Ride.verdictFrom at h
    split at h
    · rename_i hs
      have hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true := by
        cases hq : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) with
        | true => rfl
        | false => exact absurd (by simp [hs, hq]) hn
      split at h
      · rename_i s
        exact ⟨hs, hl, s, rfl, Option.some.inj h⟩
      · split at h <;> cases h
    · cases h

/-- The telling letters' decision for the proof file IS the gate. -/
theorem tell_is_gate (Z : VerifierAndGoals.PublicFiles) :
    PV.Ride.letsTell.runP (VerifierAndGoals.asDescriptionFiles Z) = FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles Z) := rfl

/-- **From the ride's two printed facts, in the ride's own letters, to an opening and a run.** -/
theorem member_of_ride {Z : VerifierAndGoals.PublicFiles} {O : ByteArray → ByteArray} {B : FlashProve.FormBytes}
    {r : Except String VerifiableInference.OnPublicFiles.SlotsBehindCutD.FastSteps}
    (hv : PV.Ride.verdictThe Z O B r = some true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hd : PV.Ride.letsTell.runP (VerifierAndGoals.asDescriptionFiles Z) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat)
      (st : ℕ → S),
      VerifierAndGoals.readFiles Z = .ok pp ∧
      Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B' ∧
      RunAt Zp c (LPFD.Full.instanceAsPlainRecord z).pub (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened st :=
  at_gate (scope_of_verdict hv).1 hd

#print axioms scope_of_verdict
#print axioms tell_is_gate
#print axioms member_of_ride

end IM
