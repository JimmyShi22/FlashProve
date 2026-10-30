-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Statement and proof read twice.
/-
AT ANY WITNESS: no Script, filling, prover or thread is named.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtLayers.lean: the honest side
of the kind "lookup" (K3): at the lookup on the calls of a group's layers, the key vectors that the
table of joints' item reads off a witness (the field fills of `AtLayers`,
Honest/K3/Law/Thread/ExchangeOuts.lean) have the joint vector of the key vectors on which the honest
lookup runs (`fills_layers`, Honest/K3/Law/Thread/ExchangeFillAt.lean). One theorem, conditional.

Hypotheses that remain. The files are in scope, read, and make the public part; the group is below
twelve; namesFit; the shape is the plan's and passes the library's test. TWO TIES ON VALUES:
witnessCellsAreTheTraces (`MatsAre`: an equation of whole functions: at the honest trace it can be met
only at the plan's own record of the link's smallness test; `lay_mats_cast`,
Johnson/Desc/First/Look/K3CallerLay.lean, pays it under `BaseAt`) and witnessWeightsAreTheIndexs
(`WeightsAre`, at every layer: wider than the proof spends, which reads four). The statement ties the
letters tail, nr and nc to nothing: the caller must.

Limits. No file shows either tie of any witness. It says nothing on what the verifier's forms are
worth. Outside the scope's scales the two families part at two shifts. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOuts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTies
import Johnson.Goal.Meaning.ServedForIn
import Johnson.Goal.Meaning.LookScope
import Johnson.HonestTrace.Joint.K3FormsLayersJoint
import Johnson.HonestTrace.Joint.K3FormsJointKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Slice (GE)
open OnBytes.HonestTrace (fromG cellOf entryOf NamesFit Tr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First.Look (Sent layLay pubAt MatsAre WeightsAre)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **At a layers' link the item's key vectors have the joint vector of the library's.**
publicFiles … publicPart: the goals' scope. group: one of the twelve. place, tail, sent, letters,
witness: letters,
as AtLayers has them. trace, index: the honest side's. witnessCellsAreTheTraces,
witnessWeightsAreTheIndexs: THE TWO
TIES ON VALUES, in the library's own named readings
(Johnson/Desc/First/Look/K3CallerLay.lean:249-259). shape: the
site's. -/
theorem lookupKeyFormsAreTheLibrarysKeysAtLayers {Cells Tok : Type}
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    {group : Nat} (groupBelowTwelve : group < 12)
    (sent : Sent) (letters : K3Letters Cells Tok) (place : PlaceL) (tail : HTailF2)
    (witness : Wit Cells Tok MsgT) (trace : Tr) (index : Cm.Idx)
    (namesFit : NamesFit publicPart trace)
    (witnessCellsAreTheTraces :
      MatsAre place tail sent letters.rad letters.oW letters.wOf letters.nr letters.nc
        (layMs place sent letters.rad letters.oW (fun j => letters.seat place.link false j.1)
          letters.arr letters.msgW witness)
        (trace (2 * group)))
    (witnessWeightsAreTheIndexs :
      WeightsAre place tail sent letters.rad letters.oW letters.wOf letters.nr letters.nc group
        (layMs place sent letters.rad letters.oW (fun j => letters.seat place.link false j.1)
          letters.arr letters.msgW witness)
        index.mat)
    (shape : OnBytes.Model.Forest.Shape) (shapeIsThePlans : shape = publicPart.y.fo)
    (shapeIsLawful : FoNums.ok shape = true) (theta : GE) :
    ∀ n, n < 2 ^ shape.v →
      OnBytes.Ends.jointKey shape
        (Cb.Fo.forK Cb.Gl.E
          (layLay (pubAt publicPart group) place.fs place.lm place.F.next place.ns tail letters.nr
            letters.nc) ()
          (Cb.Fo.zext (layMu place tail sent letters.rad letters.oW letters.wOf letters.nr
            letters.nc (fun j => letters.seat place.link false j.1) letters.arr letters.msgW
            witness))) theta n =
      OnBytes.Ends.jointKey shape
        (OnBytes.Ends.G.kvG publicPart.layers group
          (fromG publicPart (cellOf publicPart trace) (entryOf index) group)) theta n := by
  subst shapeIsThePlans
  intro n hn
  refine OnBytes.HonestTrace.joint_key_agrees_where_the_calls_agree shapeIsLawful _ _ theta
    (fun c hc Y hY => ?_) hn
  have h8 : publicPart.y.fo.NC = 8 := Meaning.P34.look_eight inScope filesRead publicPartMade
  rw [h8] at hc
  have hs : FoNums.nOf publicPart.y.fo c = Inst.Model.FFSeg.aC Inst.Model.All.DF ⟨c, hc⟩ :=
    Meaning.P34.look_sizes inScope filesRead publicPartMade ⟨c, hc⟩
  rw [hs] at hY
  rw [OnBytes.HonestTrace.fromG_cellOf namesFit index groupBelowTwelve]
  exact VerifiableInference.Desc.First.Look.K3Forms.layers_joint_key_is_kvG inScope filesRead
    publicPartMade groupBelowTwelve place.fs place.lm place.F.next _ _ witnessCellsAreTheTraces _
    witnessWeightsAreTheIndexs ⟨c, hc⟩ Y hY


end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupKeyFormsAreTheLibrarysKeysAtLayers
