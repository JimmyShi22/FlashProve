-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Conditions/KeyAtTheSeatWritten.lean: at the closed term VerifierAndGoals.theDescription, WITH THE
KEY FILE's SEAT LAID: A TENTH ROAD TO THE ROW KeySound: what is owed with enc AND rad WRITTEN: no
letter is left under the ∃. The sibling of keySound_at_rest (KeyAtTheSeat.lean), which stands.

Main names.
  RestAtSeatW Z: RestAtSeat's text with LPFD.RestOffW LPFD.paidW
    (Johnson/Top/Fire/Code/KeyAtWritten.lean) in RestOff paidNow's place.
  keySound_at_written: KeySound from RestAtSeatW: by keySound_at_off and off_of_restW. As the list
    grows this name stays.
Object: VerifierAndGoals.AtTheName.KeySound. User: keySound_of_open (KeySoundOfOpen.lean). Letters: none.

Limits. A joining: its one premise is the whole of what is then left: the laws of the rows outside
the list, at the written enc and rad. This file proves none of them. They are proved elsewhere, at
every Z in scope where protocolDataWellFormed says yes: keyOpenAt_holds (KeyOpenHolds.lean), from which
restAt_of_open (KeySoundOfOpenAt.lean) gives RestAtSeatW Z. That protocolDataWellFormed says yes at the release's
full-size public files is evaluated, not proved. The limits in KeyOpenHolds.lean's head hold here
too. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Goal.Conditions.KeyAtTheSeat
import Johnson.Top.Fire.Code.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc
open VerifiableInference.Desc.Key (Xi keyInstanceOfOutOfDomainSample Source LaterPlaces descriptionFromSource descAt descriptionFromPlan madeAt
    sourceOf
  rangesNumbers laterPlaces fixedDigest)



/-- **What is owed at the seat, with enc and rad written.** -/
def RestAtSeatW (Z : PublicFiles) : Prop :=
  ∀ (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made) (X : Source) (N : H2U.PlaceNums)
    (P : LaterPlaces),
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ →
    madeAt X₀ Z.lay fixedDigest = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N →
    laterPlaces m = .ok P →
    (descriptionFromSource X N P).data "key file" = .ok ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) →
    (descriptionFromSource X N P).planOk = true → (descriptionFromSource X N P).wantedOk = true → (descriptionFromSource X N P).owedOk = true →
    (∀ t ∈ Key.lawsAsk X₀ Z.lay m (descriptionFromSource X N P) (theKeyData (asDescriptionFiles Z)), t.2 = true) →
    (dataAtFiles flashProveData Z).G = bigReq m.p →
    LPFD.RestOffW LPFD.paidW X N P (dataAtFiles flashProveData Z).DK

/-- **The row KeySound from the laws of the rows outside the list, at no letter.** -/
theorem keySound_at_written
    (rest : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → RestAtSeatW Z) :
    KeySound :=
  keySound_at_off fun Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG =>
    LPFD.off_of_restW _ hs (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX₀) hm hX hp hN hw hD
      (pin_at_seat Z hs hl) (rest Z hs hl X₀ m X N P hX₀ hm hX hN hP hD hp hw ho ha hG)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.RestAtSeatW
#print axioms VerifierAndGoals.AtTheName.keySound_at_written
