-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/AttentionRiderVanishesAtTheHonestTrace.lean: the honest side
of the kind "lookup" (K3), at the lookup on the calls of an attention sub-proof.

Behind the lookup's step the exchange asks that the array of the caller's rider is 0 at every vertex
of its cube (the field cubes of AtAttention, K3/Law/Thread/ExchangeOuts.lean). At attention that is
the third identity: a row's denominator is the sum of the row's weights. Here it is shown of the
honest trace.

Premises: the three on the public files (in scope; the files are read; publicOf returns), "the
request is served", the group's number is below 12.

What is shown.
  denominatorsAreRowSumsAtTheHonestTrace: AttRidden at the list of the attention sub-proof of the
    group, in the honest trace (over the base field).
  denominatorsAreRowSumsInTheChallengeField: AttRidden says the same over the challenge field, at
    any shape and list.
  attentionRiderVanishesWhereDenominatorsAreRowSums: from AttRidden to "0 on the cube", at any shape
    and list, at every tuple of messages whose cells are the list's (CellsAre), where the lookup's
    record and the segment's sizes fit (AttFits; public).
  attentionRiderVanishesAtTheHonestTrace: the two joined.

Not claimed: that any tuple of messages holds the trace's cells; that AttFits holds at any record;
that a verifier's block accepts; anything on soundness, completeness or zero knowledge.
-/
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.Goal.Meaning.Row
import Johnson.Desc.First.Look.K3CallerAttMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (OracleShape)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (theTrace ServesAt meetsAll_theTrace)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Road (Hd.shapeA)
open OnBytes.Road.L5 (Zs dimOf cellsA)
open OnBytes.Road.Rows (callsOf)
open Inst.Model (Instance ppref ScalesAndPolicy)
open Inst.Model.AttSeg (Raw Idn idnVal castT)
open VerifiableInference.Desc.First.Look (Place Sent attSg attRider attCells CellsAre)

variable {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy} {layout : Option ByteArray}
  {publicRecord : OnBytes.Model.Verify.Public} {index : Cm.Idx} {request : Instance ppref}

/-- **At the honest trace of a served request every denominator is the sum of its row's weights**:
the third identity of attention is 0 at every valid name, at the list of the attention sub-proof of
the group. -/
theorem denominatorsAreRowSumsAtTheHonestTrace (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) {group : ℕ}
    (groupIsSmall : group < 12) :
    Meaning.AttRidden (Hd.shapeA publicRecord group)
      (theTrace publicRecord index request (2 * group + 1)) :=
  fun piece headGroup position valid =>
    ((meetsAll_theTrace filesAreInScope filesAreRead publicPartIsRead requestIsServed).ords.att
        group groupIsSmall).rel.2.2 (.at3 piece headGroup position) valid

/-- **The same over the challenge field**, at any shape and any list of integer matrices. -/
theorem denominatorsAreRowSumsInTheChallengeField {shape : OnBytes.Attention.Shape} {list : Zs}
    (ridden : Meaning.AttRidden shape list) (piece headGroup position : ℕ)
    (valid : (Idn.at3 piece headGroup position).Valid (dimOf shape)) :
    idnVal (dimOf shape) (castT (cellsA shape list) : Raw → Cb.Gl.E)
      (.at3 piece headGroup position) = 0 := by
  have inBase := ridden piece headGroup position valid
  rw [Inst.Model.AttSeg.idn_cast] at inBase
  rw [Inst.Model.AttSeg.idn_cast]
  exact (CharP.intCast_eq_zero_iff Cb.Gl.E Cb.Gl.p _).2
    ((CharP.intCast_eq_zero_iff Cb.Gl.F Cb.Gl.p _).1 inBase)

/-- **From "every denominator is its row's sum" to "the rider's array is 0 on its cube"**, at any
shape and list. -/
theorem attentionRiderVanishesWhereDenominatorsAreRowSums (place : Place)
    (shape : OnBytes.Attention.Shape) (tail : HTailF2) (sent : Sent) (radius : OracleShape → Nat)
    (extension : Iop.ExtSpec) (witnessPart : Type) (messages : (attSg place sent radius).Msg)
    (list : Zs) (messagesHoldTheList : CellsAre place shape tail sent radius messages list)
    (sizesFit : Cb.Rider.AttFits place.fs (dimOf shape) (callsOf place.fs))
    (ridden : Meaning.AttRidden shape list) :
    Cb.Rider.OnCubes (attRider place shape tail sent radius extension witnessPart).g
      (attRider place shape tail sent radius extension witnessPart).f () messages :=
  (Cb.Rider.den_source (dimOf shape)
      (fun (_ : Unit) messages' => attCells place shape tail sent radius messages')
    sizesFit.nb () messages).2 fun piece headGroup position valid => by
      show idnVal (dimOf shape) (attCells place shape tail sent radius messages)
        (.at3 piece headGroup position) = 0
      rw [messagesHoldTheList]
      exact denominatorsAreRowSumsInTheChallengeField ridden piece headGroup position valid

/-- **So the rider of attention's lookup is 0 on its cube**, at every tuple of messages whose cells
are those of the honest trace's list of the attention sub-proof of the group. -/
theorem attentionRiderVanishesAtTheHonestTrace (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) {group : ℕ} (groupIsSmall : group < 12)
    (place : Place) (tail : HTailF2) (sent : Sent) (radius : OracleShape → Nat)
    (extension : Iop.ExtSpec) (witnessPart : Type) (messages : (attSg place sent radius).Msg)
    (messagesHoldTheTrace : CellsAre place (Hd.shapeA publicRecord group) tail sent radius messages
      (theTrace publicRecord index request (2 * group + 1)))
    (sizesFit : Cb.Rider.AttFits place.fs (dimOf (Hd.shapeA publicRecord group))
      (callsOf place.fs)) :
    Cb.Rider.OnCubes
      (attRider place (Hd.shapeA publicRecord group) tail sent radius extension witnessPart).g
      (attRider place (Hd.shapeA publicRecord group) tail sent radius extension witnessPart).f ()
      messages :=
  attentionRiderVanishesWhereDenominatorsAreRowSums place (Hd.shapeA publicRecord group) tail sent
    radius extension witnessPart messages _
    messagesHoldTheTrace sizesFit
      (denominatorsAreRowSumsAtTheHonestTrace filesAreInScope filesAreRead publicPartIsRead
        requestIsServed groupIsSmall)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.denominatorsAreRowSumsAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.denominatorsAreRowSumsInTheChallengeField
#print axioms ProofFile.Honest.K3.Term.attentionRiderVanishesWhereDenominatorsAreRowSums
#print axioms ProofFile.Honest.K3.Term.attentionRiderVanishesAtTheHonestTrace
