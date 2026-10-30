-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/Lifted.lean: the honest sender, lifted to a wider input by the framework's
Part.lift, is the honest sender at the job whose data read the wider input through the same map.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. Definitions, and two lemmas that hold by rfl.
  jobOver           A job J whose data take an input of the type W', as a job at the input type W:
                    its data read the input through a map wit : W → W'. Its parameters P, its number
                    first and ride stay.
  lift_sendPart     For every job J and all maps see and wit: (sendPart J).lift see wit id (fun _ y
                    => y) = sendPart (jobOver J wit).
  sendRow_lifted    So the sender's row (sendRow, "our row") at the job jobOver J wit has, without
                    its simulator, the lifted sender as its one part.

Limits. The state is not narrowed: the lemmas are only for get := id and set := fun _ y => y. That
the part which a lot's honest side has at a place of a description is the sender so lifted is not
proved here; for the two lots of this folder it is proved in Lot.lean (sendLot_is_lotSide) and
LotW.lean (sendLot_is_wSide). No distribution is named.

How it fits. Part.lift is in Johnson/Desc/ProofFile/Honest/Frame.lean, sendRow in Row.lean. The
honest prover's parts at a description take that description's input. So the files on lots and on
the description (LotOf.lean, Lot.lean, LotW.lean, AtDesc*.lean) state Seated at jobOver J wit: a row
with the lifted sender is then the row that Seated requires. No file calls the two lemmas: they hold
by rfl, and the later proofs unfold the definitions themselves (sendLot_toHLot, LotOf.lean).
-/
import Johnson.SendSim.Seat.Row

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At

variable {V V' W W' X Pb : Type}

/-- A job whose data take an input of the type W', as a job at the input type W: its data read the
input through wit. Its parameters, its number first and ride stay. -/
def jobOver (J : SendJob W' X) (wit : W → W') : SendJob W X :=
  { J with data := fun w => J.data (wit w) }

/-- The honest sender at J, lifted by Part.lift along see and wit with the state unchanged, is the
honest sender at jobOver J wit. -/
theorem lift_sendPart (J : SendJob W' X) (see : V → V') (wit : W → W') :
    (sendPart (V := V') J).lift see wit id (fun _ y => y) = sendPart (V := V) (jobOver J wit) := rfl

/-- Without its simulator, our row at jobOver J wit has the lifted sender as its one part. -/
theorem sendRow_lifted (a : Place) (J : SendJob W' X) (see : V → V') (wit : W → W') :
    (sendRow (V := V) (Pb := Pb) a (jobOver J wit)).half =
      ⟨a, [(sendPart (V := V') J).lift see wit id fun _ y => y]⟩ := rfl

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.lift_sendPart
#print axioms OnBytes.SendSim.Seat.sendRow_lifted
