-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadA.lean: helper A of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: THE VALUES OF THE NINE KEYS. A WORKING FILE.

One statement. ("segmentName" lies in …AtTheHeadNames.lean, so that A1, A2 and B can import it without importing this file.)
"cornerKeyIsTheLibrarysSegmentKey": at the kind's record of cells of a list of integer matrices and an
index's matrix (P5J.listCells), at the corner of entry x and position t, each of the nine keys, read, is
H.segH of that segment at the reading readH of the same list and matrix.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHeadAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTies
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.P5J.HeadSaysOfOrd
import Johnson.Desc.Kinds.Law.KeysNoToken
import Johnson.Desc.Kinds.Law.PlaceColumn
import Johnson.Road.Ends.HeadBack
import Johnson.Goal.Meaning.HeadForInScope
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadNames
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadA1
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadA2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request Token PlaceKey lenOf)
open VerifiableInference.Desc.Kinds.Head.Law (cornerKey rd)
open VerifiableInference.OnPublicFiles

/-- **Each of the nine keys, at a corner, read, is the library's key of its segment.** -/
theorem cornerKeyIsTheLibrarysSegmentKey
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
    (matrices : OnBytes.Road.Mats ℤ) (index : Cm.Idx)
    (key : PlaceKey) (x t : Nat) (entryIsThere : x < lenOf key) (positionIsThere : t < 1024) :
    letI : Token := ⟨replyToken⟩
    rd (cornerKey (P5J.listCells publicPart.hS publicPart.HLy
        (OnBytes.Model.Verify.borderOf publicPart.y) matrices index.mat) key x t) =
      OnBytes.Ends.H.segH (headPub publicPart coveredPositions checkedTokens)
        (OnBytes.Road.Hd.readH matrices index.mat) (segmentName key) x t := by
  cases key with
  | inl normKey =>
    exact normCornerKeyIsTheLibrarysSegmentKey inScope filesRead publicPartMade
      sizesAreThePublicParts policyIsThePublicParts tableExponent planIsOk requestIsOk replyToken
      replyTokenIsInTheVocabulary coveredPositions checkedTokens coveredPositionsAreTheRequests
      positionsWithCostAreTheRequests checkedTokensAreTheRequests replyTokenIsTheCheckedOne matrices
      index normKey x t entryIsThere positionIsThere
  | inr headKey =>
    have h := headsCornerKeyIsTheLibrarysSegmentKey inScope filesRead publicPartMade
      sizesAreThePublicParts requestIsOk replyToken replyTokenIsInTheVocabulary coveredPositions
      checkedTokens coveredPositionsAreTheRequests positionsWithCostAreTheRequests
      checkedTokensAreTheRequests replyTokenIsTheCheckedOne matrices index headKey x t entryIsThere
      positionIsThere
    cases headKey <;> exact h

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.cornerKeyIsTheLibrarysSegmentKey
