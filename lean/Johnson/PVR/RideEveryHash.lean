-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PVR/RideEveryHash.lean: at every hash function of the goals' model the step-by-step form of
Johnson/PVR/RideThe.lean gives a verdict, and that verdict is the value of `VerifierAndGoals.verify` at
`atSecondHashFunction theDescription`. No hypothesis on the public files, the proof's bytes, the commitment, the
prompt or the output.
Why. `verdictThe_is_theDescription` (Johnson/PVR/RideThe.lean) says: whatever verdict is given is
`verify`'s value at `hashOf O`. It leaves open where a verdict is given, and it speaks of a function
O on bytes, while the goals draw a hash function on bit strings.
  `rideOf_ok`: where the five premises hold, the run returns steps.
  `verdictThe_some`: at every O whose answers have 32 bytes a verdict is given.
  `verdictThe_eq`: so at every such O the verdict is `some` of `verify`'s value at `hashOf O`.
  `verdictThe_of_stands`: at a hash function h and EVERY such O with `hashOf O = h`: the verdict is
    `some` of `verify`'s value at h. So it does not matter which O stands for h.
  `verify_every_hash`: at every hash function h there is such an O: `Run.oOf fun _ => h`
    (Run/OracleBitsAtLaws.lean), by `hashOf_oOf` (Johnson/Goal/Tie/HashOfEvery.lean).
Limits. No soundness: equations between two values. `verdictThe` reads the run's own result in one
case of four: where the public files are out of scope, where `protocolDataWellFormed` says no, and where the run
returns no steps and the decoder refuses the bytes, it answers `some false` from the public files, O
and the bytes alone (`verdictThe`, Johnson/PVR/RideThe.lean; `verdictFrom`,
Johnson/PVR/RideAll.lean); `verify` says no there too, by these equations. They speak of the
verdict's value alone: not of which strings are asked or how many, and not of the committer, the
prover or the extractor. That the step-by-step form is sound is not stated here: `Sound` speaks of
`verify`. Johnson/PVR/SoundOfTheForm.lean sets these equations beside `Sound`;
SoundOfTheFormEvents.lean in the same folder states soundness with the form's own decision in the
event; neither has `Sound` of a system built from the form. `Run.oOf` has no code: it undoes
`Run.toBytes` by choice, and at a byte string that `toBytes` does not reach nothing is said of its
answer; so the left side of `verify_every_hash` is no program at an abstract h. For "a term with
code" cite `verdictThe_eq`: its left side is a function of O. At the parameters `letsThe` alone: for
`letsTell` (the decisions that report) no verdict is shown to be given. One reference run
was driven by files outside this library: its tie to these theorems
is by name and statement, not by bytes.

Nothing on any distribution: that `oOf h` is uniform where h is,
is not said. Nothing on how long an evaluation takes. That compiled code computes what a term says
is the matter of Lean's compiler. At the description's own parser alone.
-/
import Johnson.PVR.RideThe
import Johnson.Goal.Tie.HashOfEvery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.Ride
open VerifierAndGoals FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.Tie OnBytes.RunA
open _root_.Run
open PV.Head (cThru sevenThru)
open PV.RunPure.Full (stepsFullAllAt)

/-- Where the five premises hold, the run returns steps. -/
theorem rideOf_ok (ℓ : Lets) (Z : PublicFiles) (O : ByteArray → ByteArray) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token)
    (hp : tiePremB (ℓ.live (asDescriptionFiles Z)) Z O B = true) :
    ∃ s, rideOf ℓ Z O B commitment prompt output = .ok s := by
  have hp' := hp
  unfold tiePremB tieRows at hp'
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hp'
  obtain ⟨_, _, hO, _, hd⟩ := hp'
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hd
  unfold rideOf
  rw [if_pos hp]
  simp only [hf]
  unfold stepsFullAllAt
  simp only [dif_pos hO]
  exact ⟨_, rfl⟩

/-- **At every O whose answers have 32 bytes a verdict is given.** -/
theorem verdictThe_some (Z : PublicFiles) (O : ByteArray → ByteArray) (h32 : ∀ b, (O b).size = 32)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) :
    ∃ b, verdictThe Z O B (rideOf letsThe Z O B commitment prompt output) = some b := by
  have hO : (cThru O (asDescriptionFiles Z)).size = 32 := size_cThru O h32 _
  have h7 : ((sevenThru O recordGround (asDescriptionFiles Z) (cThru O (asDescriptionFiles Z))).all fun b =>
      decide (b.size = 32)) = true :=
    List.all_eq_true.2 fun b hb => decide_eq_true (size_sevenThru O h32 _ _ _ b hb)
  unfold verdictThe
  cases scope : InScope Z with
  | false =>
    refine ⟨false, ?_⟩
    simp [verdictFrom, scope]
  | true =>
    cases live : protocolDataWellFormed (asDescriptionFiles Z) with
    | false =>
      refine ⟨false, ?_⟩
      simp [hO, h7]
    | true =>
      cases hd : decodeD (cThru O (asDescriptionFiles Z)) B with
      | some f =>
        have hp : tiePremB (letsThe.live (asDescriptionFiles Z)) Z O B = true := by
          show tiePremB (protocolDataWellFormed (asDescriptionFiles Z)) Z O B = true
          unfold tiePremB tieRows
          simp [scope, live, hO, h7, hd]
        obtain ⟨s, hs⟩ := rideOf_ok letsThe Z O B commitment prompt output hp
        refine ⟨s.yes, ?_⟩
        rw [hs]
        simp [verdictFrom, scope]
      | none =>
        refine ⟨false, ?_⟩
        have hp : tiePremB (letsThe.live (asDescriptionFiles Z)) Z O B = false := by
          show tiePremB (protocolDataWellFormed (asDescriptionFiles Z)) Z O B = false
          unfold tiePremB tieRows
          simp [hd]
        have hr : ∃ e, rideOf letsThe Z O B commitment prompt output = .error e := by
          unfold rideOf
          rw [if_neg (by rw [hp]; exact Bool.false_ne_true)]
          exact ⟨_, rfl⟩
        obtain ⟨e, he⟩ := hr
        rw [he]
        simp [verdictFrom, scope, hO, h7, hd]

/-- **At every such O the verdict is `verify`'s value at `hashOf O`.** -/
theorem verdictThe_eq (Z : PublicFiles) (O : ByteArray → ByteArray) (h32 : ∀ b, (O b).size = 32)
    (B : FormBytes) (commitment : Commitment) (prompt output : List Token) :
    verdictThe Z O B (rideOf letsThe Z O B commitment prompt output) =
      some ((VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z)
        commitment prompt output B).evaluate (hashOf O)) := by
  obtain ⟨b, hb⟩ := verdictThe_some Z O h32 B commitment prompt output
  rw [hb, verdictThe_is_theDescription Z O B commitment prompt output b hb]

/-- **At a hash function h and every such O that stands for it**: the verdict is `verify`'s value
at h. -/
theorem verdictThe_of_stands (Z : PublicFiles) (h : VerifiableInference.Hash) (O : ByteArray → ByteArray)
    (h32 : ∀ b, (O b).size = 32) (e : hashOf O = h) (B : FormBytes) (commitment : Commitment)
    (prompt output : List Token) :
    verdictThe Z O B (rideOf letsThe Z O B commitment prompt output) =
      some ((VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z)
        commitment prompt output B).evaluate h) :=
  e ▸ verdictThe_eq Z O h32 B commitment prompt output

/-- **AT EVERY HASH FUNCTION OF THE GOALS' MODEL: the step-by-step form's verdict is `verify`'s
value.** -/
theorem verify_every_hash (Z : PublicFiles) (h : VerifiableInference.Hash) (B : FormBytes)
    (commitment : Commitment) (prompt output : List Token) :
    verdictThe Z (_root_.Run.oOf fun _ => h) B
        (rideOf letsThe Z (_root_.Run.oOf fun _ => h) B commitment prompt output) =
      some ((VerifierAndGoals.verify (atSecondHashFunction theDescription) Z ((atSecondHashFunction theDescription).parse Z)
        commitment prompt output B).evaluate h) := by
  exact verdictThe_of_stands Z h _ (_root_.Run.size_oOf _) (hashOf_oOf h) B commitment prompt output

end PV.Ride

#print axioms PV.Ride.rideOf_ok
#print axioms PV.Ride.verdictThe_some
#print axioms PV.Ride.verdictThe_eq
#print axioms PV.Ride.verdictThe_of_stands
#print axioms PV.Ride.verify_every_hash
