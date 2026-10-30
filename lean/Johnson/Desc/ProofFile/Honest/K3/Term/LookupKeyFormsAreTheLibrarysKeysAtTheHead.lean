-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Statement and proof read twice.
/-
AT ANY WITNESS: no Script, filling, prover or thread is named.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: the honest side
of the kind "lookup" (K3): at the lookup on the calls of the output head, the key vectors that the
table of joints' item reads off a witness (the field fills of `AtHead`,
Honest/K3/Law/Thread/ExchangeHeadAll.lean: the forms "key k" of the head's own kind at corners) have
the joint vector of the key vectors on which the honest lookup runs (`fills_head`,
Honest/K3/Law/Thread/ExchangeFillAt.lean: `kvH` at the seated public record). One theorem,
conditional; eight files of helpers beside it (…AtTheHeadNames, A, A0, A1, A2, B, B0, B1).

Hypotheses that remain. The files are in scope, read, and make the public part; the plan's test
(`planOk_of_numbers` with `numbers_in_scope`, Johnson/Goal/Meaning/HeadCondScope.lean, pays it in
scope); four clauses that tie the head's request to the covered positions and the checked tokens.
replyTokenIsTheCheckedOne is asked only where the last position is checked: that the reply HEARD is
the asked token is the caller's (`replyTokenBehindTheLookupIsTheRequests`,
Honest/K3/Term/ReplyTokenBehindTheLookup.lean). TIES ON VALUES: `MatsAre` at the head's link, a total
equation over all eight matrices; the weights' tie; the trace's cells are small. The letter place is
tied to nothing: the caller must.

Limits. No file shows the ties of any witness. It says nothing on what the verifier's forms are worth.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHeadAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTies
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.P5J.HeadSaysOfOrd
import Johnson.Desc.Kinds.Law.KeysNoToken
import Johnson.Desc.Kinds.Law.PlaceColumn
import Johnson.Road.Ends.HeadBack
import Johnson.Goal.Meaning.HeadForInScope
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.Desc.Kinds.Law.LibLetters
import Johnson.Desc.Kinds.Law.CellsAlike
import Johnson.Desc.Kinds.Law.OutCall
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadA
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Slice (GE)
open OnBytes.HonestTrace (fromH cellOf entryOf NamesFit Tr)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First.Look (Sent MatsAre wOfE)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request)
open VerifiableInference.Desc.Kinds.Head.Law (headLay)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **At the head's link the item's key vectors, at the reply's token, have the joint vector of the
library's.**
sizes, policy: the library's own at the public part. request: the output head's kind's letters of
the request (tokens, first
and last checked position). replyToken: the token at which the item reads the keys (at the term:
what the verifier's state
holds as the reply heard). coveredPositions, checkedTokens: the honest side's (at the term: reqAt of
the instance,
Honest/K3/WitReq.lean:69). THE FOUR CLAUSES ON THE REQUEST tie the two; the last is the token's: it
is asked where the last
position is checked, and nowhere else. witnessCellsAreTheTraces, traceIsSmall,
witnessWeightsAreTheIndexs: THE TIES ON
VALUES. shape: the site's. -/
theorem lookupKeyFormsAreTheLibrarysKeysAtTheHead {Cells Tok : Type}
    [sizes : Sizes] [policy : Policy] [request : Request]
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart)
    (policyIsThePublicParts : policy = k3PolicyAt publicPart)
    (tableExponent : Nat)
    (planIsOk : VerifiableInference.Desc.Kinds.Head.planOk tableExponent = true)
    (requestIsOk : VerifiableInference.Desc.Kinds.Head.Request.ok = true)
    (replyToken : Nat) (replyTokenIsInTheVocabulary : replyToken <
      VerifiableInference.Desc.Kinds.Head.V)
    (coveredPositions : OnBytes.Model.Head.Covered) (checkedTokens : Array Nat)
    (coveredPositionsAreTheRequests : ∀ t, t < 1024 →
      coveredPositions.hOn.getD t false = VerifiableInference.Desc.Kinds.Head.checked t)
    (positionsWithCostAreTheRequests : ∀ t, t < 1024 →
      coveredPositions.hOnC.getD t false = VerifiableInference.Desc.Kinds.Head.costed t)
    (checkedTokensAreTheRequests : ∀ t, t + 1 < 1024 →
      VerifiableInference.Desc.Kinds.Head.checked t = true →
      checkedTokens.getD t 0 = VerifiableInference.Desc.Kinds.Head.tok (t + 1))
    (replyTokenIsTheCheckedOne : VerifiableInference.Desc.Kinds.Head.checked 1023 = true →
      checkedTokens.getD 1023 0 = replyToken)
    (sent : Sent) (letters : K3Letters Cells Tok) (place : PlaceL)
    (witness : Wit Cells Tok MsgT) (trace : Tr) (index : Cm.Idx)
    (namesFit : NamesFit publicPart trace)
    (witnessCellsAreTheTraces :
      MatsAre place publicPart.H.tl sent letters.rad letters.oW letters.wOf letters.nr letters.nc
        (layMs place sent letters.rad letters.oW (fun j => letters.seat place.link false j.1)
          letters.arr letters.msgW witness)
        (trace 24))
    (traceIsSmall : ∀ a r c, |trace 24 a r c| < 2 ^ 18)
    (witnessWeightsAreTheIndexs : ∀ a b,
      wOfE (layMu place publicPart.H.tl sent letters.rad letters.oW letters.wOf letters.nr
        letters.nc (fun j => letters.seat place.link false j.1) letters.arr letters.msgW witness)
        a b = ((index.mat a b : ℤ) : Cb.Gl.E))
    (shape : OnBytes.Model.Forest.Shape) (shapeIsThePlans : shape = publicPart.HLy.fs)
    (shapeIsLawful : FoNums.ok shape = true) (theta : GE) :
    ∀ n, n < 2 ^ shape.v →
      OnBytes.Ends.jointKey shape
        (Cb.Fo.forK Cb.Gl.E
          (headLay (k3AdrAt publicPart) place.fs place.lm place.F.next place.ns publicPart.H.tl
            letters.nr letters.nc) replyToken
          (Cb.Fo.zext (layMu place publicPart.H.tl sent letters.rad letters.oW letters.wOf
            letters.nr letters.nc (fun j => letters.seat place.link false j.1) letters.arr
            letters.msgW witness))) theta n =
      OnBytes.Ends.jointKey shape
        (OnBytes.Ends.H.kvH (headPub publicPart coveredPositions checkedTokens)
          (fromH publicPart (cellOf publicPart trace) (entryOf index))) theta n := by
  subst shapeIsThePlans
  have core := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  have numbers := _root_.Meaning.HeadS.sizes_in_scope inScope filesRead publicPartMade
  have wide : VerifiableInference.Desc.Kinds.HeadJoin.Wide := by
    subst sizesAreThePublicParts
    exact VerifiableInference.Desc.Kinds.Head.Law.Came.wide_at publicPart.hS core.full
      numbers.2.2.2.2.2.1
  have positions : VerifiableInference.Desc.Kinds.Norm.T = 1024 := by
    subst sizesAreThePublicParts
    show 2 ^ publicPart.hS.lt = 1024
    rw [numbers.1]
  -- the cells that the caller reads off the witness agree with the kind's record of the trace's list
  have same := P5J.same_listCells (h := publicPart.hS) (L := publicPart.HLy)
    (OnBytes.Model.Verify.borderOf publicPart.y) wide witnessCellsAreTheTraces traceIsSmall
    witnessWeightsAreTheIndexs
  -- the two families agree at every call that is there, at every index
  have families : ∀ q, q < publicPart.HLy.fs.NC → ∀ i,
      Cb.Fo.forK Cb.Gl.E
        (headLay (k3AdrAt publicPart) place.fs place.lm place.F.next place.ns publicPart.H.tl
          letters.nr letters.nc) replyToken
        (Cb.Fo.zext (layMu place publicPart.H.tl sent letters.rad letters.oW letters.wOf
          letters.nr letters.nc (fun j => letters.seat place.link false j.1) letters.arr
          letters.msgW witness)) q i =
      OnBytes.Ends.H.kvH (headPub publicPart coveredPositions checkedTokens)
        (fromH publicPart (cellOf publicPart trace) (entryOf index)) q i := by
    intro q callIsThere i
    letI : VerifiableInference.Desc.Kinds.Head.Token := ⟨replyToken⟩
    have facts := VerifiableInference.Desc.Kinds.Head.Law.planFacts planIsOk
    have positionIsThere : i % VerifiableInference.Desc.Kinds.Norm.T <
        VerifiableInference.Desc.Kinds.Norm.T := Nat.mod_lt _ (by rw [positions]; norm_num)
    have lengths : ∀ n ∈ (VerifiableInference.Desc.Kinds.Head.Law.callKeys q).map
        VerifiableInference.Desc.Kinds.Head.lenOf, n < 2 ^ 41 := by
      intro n membership
      obtain ⟨key, _, rfl⟩ := List.mem_map.1 membership
      exact VerifiableInference.Desc.Kinds.Head.Law.Came.lens_small planIsOk key
    show VerifiableInference.Desc.Kinds.Head.Law.rd
      (VerifiableInference.Desc.Kinds.Head.Law.keyTable
        (VerifiableInference.Desc.Kinds.Head.Law.headCells
          (VerifiableInference.Desc.Kinds.Head.Law.adrOf publicPart.hS publicPart.HLy
            (OnBytes.Model.Verify.borderOf publicPart.y)) place
          publicPart.H.tl sent letters.rad letters.oW letters.wOf letters.nr letters.nc
          (layMs place sent letters.rad letters.oW (fun j => letters.seat place.link false j.1)
            letters.arr letters.msgW witness)) q
        (i / VerifiableInference.Desc.Kinds.Norm.T) (i % VerifiableInference.Desc.Kinds.Norm.T)) = _
    rw [← VerifiableInference.Desc.Kinds.Head.Law.Came.keyTable_same same facts requestIsOk
      replyTokenIsInTheVocabulary q _ positionIsThere, OnBytes.HonestTrace.fromH_cellOf namesFit index]
    unfold VerifiableInference.Desc.Kinds.Head.Law.keyTable
      VerifiableInference.Desc.Kinds.Head.Law.callTable
    rw [VerifiableInference.Desc.Kinds.Head.Law.Came.tableOf_map
      VerifiableInference.Desc.Kinds.Head.Law.rd lengths,
      VerifiableInference.Desc.Kinds.Head.Law.rd_natCast, positions]
    exact callTableIsTheLibrarysKeyVector inScope filesRead publicPartMade sizesAreThePublicParts coveredPositions
      checkedTokens
      (fun key x t => VerifiableInference.Desc.Kinds.Head.Law.rd
        (VerifiableInference.Desc.Kinds.Head.Law.cornerKey
          (P5J.listCells publicPart.hS publicPart.HLy (OnBytes.Model.Verify.borderOf publicPart.y)
            (trace 24) index.mat) key x t))
      (OnBytes.Ends.H.segH (headPub publicPart coveredPositions checkedTokens)
        (OnBytes.Road.Hd.readH (trace 24) index.mat))
      (fun key x t entryIsThere positionBelow =>
        cornerKeyIsTheLibrarysSegmentKey inScope filesRead publicPartMade sizesAreThePublicParts
          policyIsThePublicParts tableExponent
          planIsOk requestIsOk replyToken replyTokenIsInTheVocabulary coveredPositions checkedTokens
          coveredPositionsAreTheRequests positionsWithCostAreTheRequests checkedTokensAreTheRequests
          replyTokenIsTheCheckedOne (trace 24) index key x t entryIsThere positionBelow)
      q callIsThere i
  obtain ⟨_, callOfATree, _⟩ := Cb.Fo.ok_parts shapeIsLawful
  intro n _
  unfold OnBytes.Ends.jointKey
  dsimp only
  split
  · rename_i treeIsThere
    exact congrArg (fun z => z + _) (families _ (callOfATree _ treeIsThere).1 _)
  · rfl


end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupKeyFormsAreTheLibrarysKeysAtTheHead
