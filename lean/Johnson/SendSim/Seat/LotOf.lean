-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/LotOf.lean: a lot of the sender's rows (sendRow, "our rows"), made of any list
of jobs. Without the simulators it is the lot that has, at each job's place, the honest sender
lifted to the prover's input.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. jobs is any list of jobs, as a function of the public part and the ground, whose
data take an input of a type W'. wit is any map from the prover's input type W to W'.
  sendLot           The lot of rows (SLot) that has, for each job J of the list, our row sendRow at
                    J's place and at the job jobOver J wit.
  sendLot_toHLot    Proved here. Without the simulators (SLot.toHLot), sendLot name wit jobs is the
                    lot of the same name that has liftedHalf wit J for each job J.
  liftedHalf        At J's place, one part: the sender sendPart J, lifted by Part.lift along id and
                    wit, with the state unchanged.
  seated_lifted     Proved here. If Side.seated returns a side for such a row, and its sub-protocol
                    has K1's two rounds and oracle messages at J.P, the side is Seated at jobOver J
                    wit.
  over_P, over_ride, over_first   By rfl: jobOver changes neither P, nor ride, nor first. So the
                    test sendFits is the same at J and at jobOver J wit.

Limits. That the honest side of a given lot is liftedHalf of a list of jobs is not proved here: it
depends on that lot's definition. For the two lots of this folder it is proved in Lot.lean and
LotW.lean. The state is not narrowed. Each row has one part. Of a sub-protocol that is guarded, or
joined with another, the file uses only the rounds and oracle messages. No distribution is named.

How it fits. SLot and SLot.toHLot are in Johnson/Desc/ProofFile/Honest/Thread/Rows.lean, sendRow in
Row.lean, jobOver in Lifted.lean. If a lot's honest side is written as liftedHalf of a list of jobs,
our lot is that honest side with a simulator added to each part. Lot.lean and LotW.lean apply
sendLot and sendLot_toHLot to the two lots of Spec.fieldsAtLots. seated_lifted serves seatedAt_own
and seatedAt_w (AtDesc.lean) and seated_of_block (Lot.lean). No file calls over_P, over_ride or
over_first: they are there to state that sendFits is the same at J and at jobOver J wit.
-/
import Johnson.SendSim.Seat.Lifted

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At

variable {S Cl V W W' X Pb : Type}

/-- At J's place, one part without a simulator: the honest sender at J, lifted by Part.lift along id
and wit with the state unchanged. -/
def liftedHalf (wit : W → W') (J : SendJob W' X) : Placed V W X :=
  ⟨J.P.place, [(sendPart (V := V) J).lift id wit id fun _ y => y]⟩

/-- The lot of rows that has, for each job J of the list, our row at J's place and at the job
jobOver J wit. -/
def sendLot (name : String) (wit : W → W') (jobs : ProofFile.Pub → ProofFile.Ground → List (SendJob W' X)) :
    SLot V W X Pb :=
  ⟨name, fun Z G => (jobs Z G).map fun J => sendRow J.P.place (jobOver J wit)⟩

/-- Without the simulators (SLot.toHLot), sendLot is the lot of the same name that has liftedHalf
wit J for each job J. -/
theorem sendLot_toHLot (name : String) (wit : W → W')
    (jobs : ProofFile.Pub → ProofFile.Ground → List (SendJob W' X)) :
    (sendLot (V := V) (Pb := Pb) name wit jobs).toHLot =
      ⟨name, fun Z G => (jobs Z G).map (liftedHalf wit)⟩ := by
  show (⟨name, fun Z G => ((jobs Z G).map fun J =>
    sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).map (·.half)⟩ : HLot V W X) = _
  congr 1
  funext Z G
  rw [List.map_map]
  rfl

/-- jobOver does not change the parameters P. -/
theorem over_P (J : SendJob W' X) (wit : W → W') : (jobOver J wit).P = J.P := rfl

/-- jobOver does not change ride. -/
theorem over_ride (J : SendJob W' X) (wit : W → W') : (jobOver J wit).ride = J.ride := rfl

/-- jobOver does not change the number first. -/
theorem over_first (J : SendJob W' X) (wit : W → W') : (jobOver J wit).first = J.first := rfl

/-- If Side.seated returns a side for our row at J's place and at jobOver J wit, and that side's
sub-protocol has K1's two rounds and oracle messages at J.P, the side is Seated at jobOver J wit. -/
theorem seated_lifted {bs : List (Block S Cl)} {fs₀ : List (Fall S)} {σ₀ : Side S Cl V W X Pb}
    (J : SendJob W' X) (wit : W → W')
    (hσ : Side.seated bs (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
      (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs₀ = some σ₀)
    (hr : σ₀.block.rounds = K1.rounds J.P) (ho : σ₀.block.oracles = K1.oracles J.P) :
    Seated σ₀ (jobOver J wit) := seated_at hσ hr ho

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.sendLot_toHLot
#print axioms OnBytes.SendSim.Seat.seated_lifted
