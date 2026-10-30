-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadA0.lean: helper A0 of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: THE GROUND THAT THE NINE VALUES SHARE. A WORKING FILE.

"requestRecord": the kind's letters of the request and the policy as the library's record of a request.
"lettersAtTheHead": in scope, at the public part's sizes: the kind's letters are the library's numbers
(Same, Wide, More of Johnson/Desc/Kinds/Law/LibJoin.lean). "librarysTiesAtTheHead": the library's record
TiesH (Johnson/Road/Ends/HeadSeg.lean) at headPub and readH, so that key_segH spells every H.segH as the
specification's key. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHeadAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTies
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.P5J.HeadSaysOfOrd
import Johnson.Desc.Kinds.Law.KeysNoToken
import Johnson.Desc.Kinds.Law.PlaceColumn
import Johnson.Desc.Kinds.Law.LibLetters
import Johnson.Road.Ends.HeadBack
import Johnson.Road.Ends.HeadWit
import Johnson.Goal.Meaning.HeadForInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request Token PlaceKey lenOf)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More)
open VerifiableInference.OnPublicFiles
open OnBytes.Road (Hd.TiesH Hd.readH Hd.cellsH Hd.npOf)

/-- The kind's letters of the request and of the policy, as the library's record of a request. -/
def requestRecord [Sizes] [Policy] [Request] [Token] : Inst.Model.Head.Req :=
  ⟨VerifiableInference.Desc.Kinds.Head.r, VerifiableInference.Desc.Kinds.Head.e,
    VerifiableInference.Desc.Kinds.Head.win,
    ⟨VerifiableInference.Desc.Kinds.Head.C, VerifiableInference.Desc.Kinds.Head.theta,
      VerifiableInference.Desc.Kinds.Head.cap⟩⟩

/-- A run's record with the public part's shape and layout, and the given positions and tokens. -/
def runRecord (publicPart : OnBytes.Model.Verify.Public)
    (coveredPositions : OnBytes.Model.Head.Covered) (checkedTokens : Array Nat) :
    OnBytes.Model.Head.Run :=
  { OnBytes.Road.Hd.blankRun publicPart with
    cov := coveredPositions
    x := { (OnBytes.Road.Hd.blankRun publicPart).x with win := checkedTokens } }

theorem headPub_is_pubH (publicPart : OnBytes.Model.Verify.Public)
    (coveredPositions : OnBytes.Model.Head.Covered) (checkedTokens : Array Nat) :
    headPub publicPart coveredPositions checkedTokens =
      OnBytes.Road.Hd.pubH (runRecord publicPart coveredPositions checkedTokens)
        (OnBytes.Model.Verify.borderOf publicPart.y) publicPart.layers.wsLay := rfl

/-- **In scope the kind's letters are the library's numbers.** -/
theorem lettersAtTheHead
    [sizes : Sizes] [policy : Policy] [request : Request]
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart)
    (replyToken : Nat) :
    letI : Token := ⟨replyToken⟩
    Same requestRecord ∧ Wide ∧ More requestRecord := by
  subst sizesAreThePublicParts
  have B := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  have h24 := Meaning.HeadS.famF_in_scope inScope filesRead publicPartMade
  have Wd := VerifiableInference.Desc.Kinds.Head.Law.Came.wide_at publicPart.hS B.full h24
  letI : Sizes := k3SizesAt publicPart
  letI : Token := ⟨replyToken⟩
  have hT : VerifiableInference.Desc.Kinds.Norm.T = 1024 := by
    show 2 ^ publicPart.hS.lt = 1024
    rw [B.full.lt]
  have hJVa : VerifiableInference.Desc.Kinds.Head.JVa = 131072 := by
    have hJV : VerifiableInference.Desc.Kinds.Head.JV = 202048 := Wd.JV
    unfold VerifiableInference.Desc.Kinds.Head.JVa
    rw [hJV]
    rfl
  exact ⟨⟨hT, rfl, rfl, rfl, rfl, rfl⟩, Wd, ⟨B.sh, hJVa, fun _ => rfl⟩⟩

/-- **The library's ties at the head's public data and the reading of a list of matrices.** -/
theorem librarysTiesAtTheHead
    [sizes : Sizes] [policy : Policy] [request : Request]
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart)
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
    (matrices : OnBytes.Road.Mats ℤ) (weights : Inst.Model.Mat) :
    letI : Token := ⟨replyToken⟩
    Hd.TiesH (headPub publicPart coveredPositions checkedTokens) (Hd.readH matrices weights)
      OnBytes.Road.HeadSizes.ref (Hd.npOf publicPart.hS)
      ((Hd.cellsH publicPart.hS publicPart.HLy (OnBytes.Model.Verify.borderOf publicPart.y)
        matrices).cast Cb.Gl.E)
      (fun j v => (((Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef
        weights).H j v : ℤ) : Cb.Gl.E))
      requestRecord := by
  obtain ⟨S, Wd, M⟩ := lettersAtTheHead inScope filesRead publicPartMade sizesAreThePublicParts
    replyToken
  letI : Token := ⟨replyToken⟩
  have B := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  obtain ⟨-, -, -, -, -, -, -, -, Zw, -, hlw, -⟩ :=
    Meaning.P34.pub34_public inScope filesRead publicPartMade
  have hy : OnBytes.Model.Head.layout publicPart.hS OnBytes.Road.Hd.tauFCw = .ok publicPart.HLy := by
    rw [← OnBytes.Road.Hd.tauFC_of_layout B.lay]
    exact B.head
  have hT : VerifiableInference.Desc.Kinds.Norm.T = 1024 := S.T
  have Rq : OnBytes.Road.Hd.ReqFits (runRecord publicPart coveredPositions checkedTokens)
      OnBytes.Road.HeadSizes.ref requestRecord := by
    refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hon => ?_⟩
    · rw [VerifiableInference.Desc.Kinds.HeadJoin.rho_eq S i]
      show _ = if coveredPositions.hOn.getD i false = true then 1 else 0
      rw [coveredPositionsAreTheRequests i hi]
    · show requestRecord.rhoC i = if coveredPositions.hOnC.getD i false = true then 1 else 0
      rw [VerifiableInference.Desc.Kinds.HeadJoin.rhoC_eq S i, positionsWithCostAreTheRequests i hi]
    · have hon' : coveredPositions.hOn.getD i false = true := hon
      rw [coveredPositionsAreTheRequests i hi] at hon'
      have hi' : i < 1024 := hi
      show VerifiableInference.Desc.Kinds.Head.win i = checkedTokens.getD i 0
      unfold VerifiableInference.Desc.Kinds.Head.win
      rw [hT]
      by_cases h1 : i + 1 < 1024
      · rw [if_pos h1, checkedTokensAreTheRequests i h1 hon']
      · have e : i = 1023 := by omega
        subst e
        rw [if_neg h1, replyTokenIsTheCheckedOne hon']
        rfl
  rw [headPub_is_pubH]
  exact OnBytes.Road.Hd.tiesH_of
    (OnBytes.Road.Hd.laid_ref hy B.full.lt B.full.d B.full.V rfl rfl) Rq B.full.XL rfl B.sh
    (Meaning.HeadS.border_in_scope inScope filesRead publicPartMade)
    (fun i => by
      have h := VerifiableInference.Desc.Kinds.Head.Law.win_lt requestIsOk
        replyTokenIsInTheVocabulary i
      rw [Wd.V] at h
      exact h)
    (fun k v hk hv => OnBytes.Road.Hd.wH_read Zw hlw _ _ matrices weights hk hv)

/-- The factor that the verifier's third digit of a margin bears; 1 at the other eight families. -/
def familyFactor (P : OnBytes.Ends.H.PubH) : Inst.Model.Head.Fam → Cb.Gl.E
  | .HD0 => OnBytes.Ends.H.iw P
  | _ => 1

/-- **The library's key of a segment is the cast of the specification's integer key** (times the factor at
the margin's third digit), at the cells of the list of matrices. -/
theorem librarysSegmentKeyIsACast
    [sizes : Sizes] [policy : Policy] [request : Request]
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart)
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
    (matrices : OnBytes.Road.Mats ℤ) (weights : Inst.Model.Mat)
    (family : Inst.Model.Head.Fam) (x t : Nat) (entryIsThere : x < Inst.Model.Head.len family)
    (positionIsThere : t < 1024) :
    letI : Token := ⟨replyToken⟩
    OnBytes.Ends.H.segH (headPub publicPart coveredPositions checkedTokens)
        (Hd.readH matrices weights) (OnBytes.Road.Hd.nameOf family) x t =
      familyFactor (headPub publicPart coveredPositions checkedTokens) family *
        ((Policy.LedgerHead.key (Hd.npOf publicPart.hS)
          (Hd.cellsH publicPart.hS publicPart.HLy (OnBytes.Model.Verify.borderOf publicPart.y)
            matrices)
          (Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef weights).H
          requestRecord family x t : ℤ) : Cb.Gl.E) := by
  have Ti := librarysTiesAtTheHead inScope filesRead publicPartMade sizesAreThePublicParts
    requestIsOk replyToken replyTokenIsInTheVocabulary coveredPositions checkedTokens
    coveredPositionsAreTheRequests positionsWithCostAreTheRequests checkedTokensAreTheRequests
    replyTokenIsTheCheckedOne matrices weights
  letI : Token := ⟨replyToken⟩
  rw [Ti.key_segH family x t (by rw [OnBytes.Road.HeadSizes.len_ref]; exact entryIsThere)
    positionIsThere]
  have e := Policy.LedgerHead.map_key (Int.castRingHom Cb.Gl.E) (Hd.npOf publicPart.hS)
    (Hd.cellsH publicPart.hS publicPart.HLy (OnBytes.Model.Verify.borderOf publicPart.y) matrices)
    (Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef weights).H
    requestRecord family x t
  have e' : ((Policy.LedgerHead.key (Hd.npOf publicPart.hS)
      (Hd.cellsH publicPart.hS publicPart.HLy (OnBytes.Model.Verify.borderOf publicPart.y) matrices)
      (Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef weights).H
      requestRecord family x t : ℤ) : Cb.Gl.E) = _ := e
  rw [e', ← OnBytes.Road.HeadSizes.key_ref]
  cases family with
  | HD0 => rfl
  | _ => exact (one_mul _).symm

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.librarysSegmentKeyIsACast
#print axioms ProofFile.Honest.K3.Term.lettersAtTheHead
#print axioms ProofFile.Honest.K3.Term.librarysTiesAtTheHead
