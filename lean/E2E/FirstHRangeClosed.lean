-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHRangeClosed.lean: the closed premises of `wit_is_job` (E2E/FirstHRangeLots.lean), in scope.

  `msgFull`'s message 0: `msg0Full`, its two counts, and that no coin lies in its main rows.
  `carry_written`: by the kernel, at `fullPub`: the book carries the sender's stretch to the test.
  `msg_zero`, `msg_shape`, `carry_fits`: at the value.

Limits. At the written sizes. Nothing on any property.
-/
import E2E.FirstHRangeLots
import E2E.FirstHPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (Source LaterPlaces sendingPar pieces)
open Johnson.Prover.Send (shapeAt)
open AtPublicFiles.KeyThread (rangesTestJob)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (oneF six_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull rideMsg rngPlace msgPlace)
open AtPublicFiles.KeyValues (matrixEntryOf multiplicitiesGroups multiplicitiesSending oneOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (dueR stepsOf dueMsg)

/-- A test's plan stands at its place. -/
theorem p12_place (a : VerifiableInference.Desc.Place) (x : H2U.PlaceNums) :
    (H2U.proximityTestParametersAt a x).place = a := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

/-- The shape of message 0 of the multiplicities' sending. -/
def msg0Full : OracleShape := ((Wf.messageOf oneF.ranges).getD 0 default).shape

/-- Its count. -/
def msg0Due : Due := dueMsg oneF.codes msg0Full none

/-- The sending's count. -/
def msgDue : Due := dueR msgFull rideMsg

theorem word_full : (stepsOf oneF.codes msg0Full none).word = 0 := by decide +kernel
theorem pad_full : (stepsOf oneF.codes msg0Full none).pad = 0 := by decide +kernel

/-- **The book carries the sender's stretch to the test.** -/
theorem carry_written :
    atFull (fun K => CarryFits (keyBook K) ⟨rngPlace, 1⟩ ⟨msgPlace, 0⟩ msg0Due msgDue) = true := by
  decide +kernel

variable {W₀ Rc X₀ X' Wk : Type} {K₀ : KeyPub} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Z : PublicFiles}

/-- A sending's shape at number 0, and its count, read its codes and messages alone. -/
theorem dueR_par (a a' : OneTime) (n n' : Nat) (w w' : String) (m : Array OracleNotice)
    (g g' : List (List Nat)) (hc : a.codes = a'.codes) (ride : Nat → Option ProofFile.Honest.K1.Ride) :
    dueR (sendingPar a n w m g) ride = dueR (sendingPar a' n' w' m g') ride := by
  unfold dueR ProofFile.Honest.K1.startR shapeAt
  simp only [AtPublicFiles.KeyLookup.sent_par]
  simp only [sendingPar, hc]

theorem msg_shape (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) : shapeAt K.msg.P 0 = msg0Full := by
  have hr : (oneOf Xs).ranges = oneF.ranges := (six_sourced hs scope).ranges
  rw [hp.msg]
  show shapeAt (sendingPar (oneOf Xs) _ _ (Wf.messageOf (oneOf Xs).ranges) _) 0 = _
  unfold shapeAt msg0Full
  rw [AtPublicFiles.KeyLookup.sent_par, hr]

theorem msg_zero (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) : MsgZero K.msg := by
  have hc : (oneOf Xs).codes = oneF.codes := (six_sourced hs scope).codes
  have hsh := msg_shape hs scope hp
  have hcodes : K.msg.P.codes = oneF.codes := by
    rw [hp.msg]
    exact hc
  have hr : K.msg.ride 0 = none := by
    rw [hp.msg]
    rfl
  refine ⟨?_, ?_, hr⟩
  · rw [hcodes, hsh, hr]
    exact word_full
  · rw [hcodes, hsh, hr]
    exact pad_full

theorem carry_fits (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (hK : fullPub = some K₀)
    (hp : FirstPublic (Pl := Pl) Xs N K f) :
    CarryFits (keyBook K₀) ⟨(rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0).p.place, 1⟩
      ⟨K.msg.P.place, 0⟩ (dueMsg K.msg.P.codes (shapeAt K.msg.P 0) (K.msg.ride 0))
      (dueR K.msg.P K.msg.ride) = true := by
  have hc : (oneOf Xs).codes = oneF.codes := (six_sourced hs scope).codes
  have hr : (oneOf Xs).ranges = oneF.ranges := (six_sourced hs scope).ranges
  have hsh := msg_shape hs scope hp
  have e1 : dueMsg K.msg.P.codes (shapeAt K.msg.P 0) (K.msg.ride 0) = msg0Due := by
    have hcodes : K.msg.P.codes = oneF.codes := by
      rw [hp.msg]
      exact hc
    have hride : K.msg.ride 0 = none := by
      rw [hp.msg]
      rfl
    rw [hcodes, hsh, hride]
    rfl
  have e2 : dueR K.msg.P K.msg.ride = msgDue := by
    rw [hp.msg]
    show dueR (sendingPar (oneOf Xs) _ _ (Wf.messageOf (oneOf Xs).ranges) _) rideMsg = _
    rw [hr, dueR_par _ oneF _ 0 _ "" _ _ [] hc]
    rfl
  have e3 : K.msg.P.place = msgPlace := by
    rw [hp.msg]
    rfl
  have e4 : (rangesTestJob (X' := X') Xs N Pl (matrixEntryOf (Rc := Rc) f) (multiplicitiesGroups Xs) 0).p.place = rngPlace :=
    p12_place _ _
  rw [e1, e2, e3, e4]
  exact of_atFull carry_written hK

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.p12_place
#print axioms AtPublicFiles.FirstH.word_full
#print axioms AtPublicFiles.FirstH.pad_full
#print axioms AtPublicFiles.FirstH.carry_written
#print axioms AtPublicFiles.FirstH.dueR_par
#print axioms AtPublicFiles.FirstH.msg_shape
#print axioms AtPublicFiles.FirstH.msg_zero
#print axioms AtPublicFiles.FirstH.carry_fits
