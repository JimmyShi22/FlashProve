-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/SelectorsAreOneHotAtTheHonestTrace.lean: the honest side of
the kind "lookup" (K3), at the lookup on the calls of a group of layers.

Behind the lookup's step the exchange asks that each array of the caller's rider is 0 at every
vertex of its cube (the field cubes of AtLayers, K3/Law/Thread/ExchangeOuts.lean). At the layers
that is the identity (J10) on the routers' selectors. Here it is shown of the honest trace.

Premises: the three on the public files (in scope; the files are read; publicOf returns), "the
request is served", the group's number is below 12.

What is shown.
  selectorsAreOneHotAtTheHonestTrace: HotField at the list of the group, in the honest trace.
  layersRiderVanishesAtTheHonestTrace: so the rider's arrays are 0 on their cubes, at every tuple of
    messages whose cells are that list's (MatsAre).

Not claimed: that any tuple of messages holds the trace's cells; that a verifier's block accepts;
anything on soundness, completeness or zero knowledge.
-/
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.Road.Rows.LayerTop
import Johnson.Desc.First.Look.K3CallerMeans
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HotOnCubes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (OracleShape)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (theTrace ServesAt meetsAll_theTrace)
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Road.Rows.Norms (HotField layer_fields)
open Inst.Model (Instance ppref ScalesAndPolicy)
open VerifiableInference.Desc.First.Look (Place Sent laySg layRider MatsAre pubAt)

variable {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy} {layout : Option ByteArray}
  {publicRecord : OnBytes.Model.Verify.Public} {index : Cm.Idx} {request : Instance ppref}

/-- **At the honest trace of a served request every router's selector is one-hot**: the identity
(J10) is 0 at every valid name, at the list of the group. -/
theorem selectorsAreOneHotAtTheHonestTrace (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) {group : ℕ}
    (groupIsSmall : group < 12) :
    HotField (layerShape publicRecord.P) publicRecord.layers.sc publicRecord.y group
      (theTrace publicRecord index request (2 * group)) index.mat request :=
  (layer_fields
      ((meetsAll_theTrace filesAreInScope filesAreRead publicPartIsRead requestIsServed).ords.layer
        group groupIsSmall)).2.2.1

/-- **So the rider of the layers' lookup is 0 on its cubes**, at every tuple of messages whose cells
are those of the honest trace's list of the group. -/
theorem layersRiderVanishesAtTheHonestTrace (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) {group : ℕ} (groupIsSmall : group < 12)
    (place : Place) (tail : HTailF2) (sent : Sent) (radius : OracleShape → Nat)
    (weightsOracle : Cb.OMsg Cb.Gl.E) (weightsReading : weightsOracle.Msg → Nat → Nat → Cb.Gl.E)
    (weightRows weightColumns : Nat) (extension : Iop.ExtSpec) (witnessPart : Type)
    (messages : (laySg place sent radius weightsOracle).Msg)
    (messagesHoldTheTrace : MatsAre place tail sent radius weightsOracle weightsReading weightRows
      weightColumns messages (theTrace publicRecord index request (2 * group))) :
    Cb.Rider.OnCubes
      (layRider place (pubAt publicRecord group) tail sent radius weightsOracle weightsReading
        weightRows weightColumns extension witnessPart).g
      (layRider place (pubAt publicRecord group) tail sent radius weightsOracle weightsReading
        weightRows weightColumns extension witnessPart).f () messages :=
  Law.Exchange.hot_onCubes place (pubAt publicRecord group) tail sent radius weightsOracle
    weightsReading weightRows weightColumns extension witnessPart messages _ messagesHoldTheTrace
    index.mat request
      (selectorsAreOneHotAtTheHonestTrace filesAreInScope filesAreRead publicPartIsRead
        requestIsServed groupIsSmall)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.selectorsAreOneHotAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.layersRiderVanishesAtTheHonestTrace
