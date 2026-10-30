-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadA2.lean: helper A2 of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: THE FINAL NORMALISATION's FOUR KEYS. A WORKING FILE.

Two theorems. "normCornerKeyIsTheLibrarysSegmentKey": the statement of helper A at the four keys, by a call of the
first at helper A0's ties and letters. "normKeyIsTheLibrarysSegmentKeyUnderTies", at letters: at any record of cells c of the output head's
kind, any public data P of the library's key vector and any reading cell of its names that are tied
(OnBytes.Road.Hd.TiesH, Johnson/Road/Ends/HeadSeg.lean) to the library's record of c's cells, at the library's
sizes: each of the four keys remLow, remHigh, clamp, digits at the corner of entry x and position t, read, is
H.segH of its segment NF, NFH, CNF, ROW.

How. Left: rd_keyN_remLow | _remHigh | _clamp | _digits (Johnson/Desc/Kinds/Law/NormProof.lean): the key, read, is
the cast of an integer term. Right: TiesH.key_segH, HeadSizes.key_ref, keyN_cast: H.segH is the cast of
Policy.LedgerHead.key on the integer cells. The two integer terms are one by xv_eq, nw_eq, rn_eq, nrm_eq, Dv_at,
Dv_eq (Johnson/Desc/Kinds/Law/LibJoinNorm.lean) and mul_eq_mu.
Limits. In the theorem at letters the ties, the two sizes, the blocks' size and the shift are premises.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadNames
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadA0
import Johnson.Desc.Kinds.HeadOutLaw
import Johnson.Desc.Kinds.Law.LibJoinNorm
import Johnson.Road.Ends.HeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request Token PlaceKey lenOf)
open VerifiableInference.Desc.Kinds.Head.Law (cornerKey rd NCells keyNAt cornerN)
open VerifiableInference.Desc.Kinds.HeadJoin (cellsN)
open OnBytes.Road
open OnBytes.Road.Hd (TiesH)
open VerifiableInference.OnPublicFiles

/-- **Each of the final normalisation's four keys, at a corner, read, is the library's key of its segment**, under
the ties between the reading of names and the kind's cells. -/
theorem normKeyIsTheLibrarysSegmentKeyUnderTies
    [Sizes] [Policy] [Request] [Token]
    {publicData : OnBytes.Ends.H.PubH} {reading : OnBytes.Ends.H.NameH → Cb.Gl.E}
    {normNumbers : Inst.Model.NormPar} {cells : NCells} {headWeights : Nat → Nat → Int}
    {libraryRequest : Inst.Model.Head.Req}
    (ties : TiesH publicData reading HeadSizes.ref normNumbers ((cellsN cells).cast Cb.Gl.E)
      (fun j v => ((headWeights j v : Int) : Cb.Gl.E)) libraryRequest)
    (positionsAre1024 : Norm.T = 1024) (widthIs5120 : Norm.d = 5120)
    (blocksDivideTheWidth : Norm.S2 ∣ Norm.d) (shiftIsTheNormNumbers : FinalNorm.KF = normNumbers.K)
    (key : FinalNorm.Key) (x t : Nat) (entryIsThere : x < lenOf (.inl key))
    (positionIsThere : t < 1024) :
    rd (cornerKey cells (.inl key) x t) =
      OnBytes.Ends.H.segH publicData reading (segmentName (.inl key)) x t := by
  have ht : t < Norm.T := by rw [positionsAre1024]; exact positionIsThere
  have libraryKey : ∀ (s : Inst.Model.Head.Fam), s ≠ .HD0 → x < HeadSizes.len HeadSizes.ref s →
      OnBytes.Ends.H.segH publicData reading (OnBytes.Road.Hd.nameOf s) x t =
        ((_root_.Policy.LedgerHead.key normNumbers (cellsN cells) headWeights libraryRequest s x t : Int) :
          Cb.Gl.E) := by
    intro s hs hx
    rw [ties.key_segH s x t hx positionIsThere,
      ← VerifiableInference.Desc.Kinds.HeadJoin.keyN_cast, ← HeadSizes.key_ref]
    cases s <;> first | exact absurd rfl hs | rfl
  cases key with
  | remLow =>
    have hx : x < Norm.d := entryIsThere
    show rd (keyNAt cells (cornerN x t) .remLow) = OnBytes.Ends.H.segH publicData reading "NF" x t
    rw [VerifiableInference.Desc.Kinds.Head.Law.rd_keyN_remLow ht blocksDivideTheWidth hx,
      show OnBytes.Ends.H.segH publicData reading "NF" x t = _ from
        libraryKey .NF (by decide) (by rw [widthIs5120] at hx; exact hx)]
    refine congrArg _ ?_
    show _ = Inst.Model.Head.xv (cellsN cells) x t *
        Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv (cellsN cells) n t) +
        2 ^ (normNumbers.K - 1) - 2 ^ normNumbers.K * Inst.Model.Head.nw (cellsN cells) x t -
        2 ^ 16 * Inst.Model.Head.rn (cellsN cells) x t
    rw [VerifiableInference.Desc.Kinds.HeadJoin.xv_eq widthIs5120,
      VerifiableInference.Desc.Kinds.HeadJoin.Dv_eq,
      VerifiableInference.Desc.Kinds.HeadJoin.nw_eq widthIs5120,
      VerifiableInference.Desc.Kinds.HeadJoin.rn_eq widthIs5120, ← shiftIsTheNormNumbers]
    rfl
  | remHigh =>
    have hx : x < Norm.d := entryIsThere
    show rd (keyNAt cells (cornerN x t) .remHigh) = OnBytes.Ends.H.segH publicData reading "NFH" x t
    rw [VerifiableInference.Desc.Kinds.Head.Law.rd_keyN_remHigh ht blocksDivideTheWidth hx,
      show OnBytes.Ends.H.segH publicData reading "NFH" x t = _ from
        libraryKey .NFH (by decide) (by rw [widthIs5120] at hx; exact hx)]
    refine congrArg _ ?_
    show _ = ((2 ^ (32 - normNumbers.K) : Nat) : Int) * Inst.Model.Head.rn (cellsN cells) x t
    rw [VerifiableInference.Desc.Kinds.HeadJoin.rn_eq widthIs5120, ← shiftIsTheNormNumbers]
    simp [Inst.Model.Site.high]
  | clamp =>
    have hx : x < Norm.d := entryIsThere
    show rd (keyNAt cells (cornerN x t) .clamp) = OnBytes.Ends.H.segH publicData reading "CNF" x t
    rw [VerifiableInference.Desc.Kinds.Head.Law.rd_keyN_clamp ht blocksDivideTheWidth hx,
      show OnBytes.Ends.H.segH publicData reading "CNF" x t = _ from
        libraryKey .CNF (by decide) (by rw [widthIs5120] at hx; exact hx)]
    refine congrArg _ ?_
    show _ = (Inst.Model.Head.nw (cellsN cells) x t + 2 ^ 15) +
      2 ^ 28 * (Inst.Model.Head.nrm (cellsN cells) x t + 2 ^ 11)
    rw [VerifiableInference.Desc.Kinds.HeadJoin.nw_eq widthIs5120,
      VerifiableInference.Desc.Kinds.HeadJoin.nrm_eq widthIs5120]
  | digits =>
    have hx : x < NR + 21 := entryIsThere
    show rd (keyNAt cells (cornerN x t) .digits) = OnBytes.Ends.H.segH publicData reading "ROW" x t
    rw [VerifiableInference.Desc.Kinds.Head.Law.rd_keyN_digits ht hx,
      show OnBytes.Ends.H.segH publicData reading "ROW" x t = _ from libraryKey .ROW (by decide) hx]
    refine congrArg _ ?_
    show _ = (Inst.Model.Ledger.mu x : Int) * Inst.Model.Head.Dv (cellsN cells) x t
    rw [VerifiableInference.Desc.Kinds.Head.Law.mul_eq_mu,
      VerifiableInference.Desc.Kinds.HeadJoin.Dv_at]

/-- **Each of the final normalisation's four keys, at a corner, read, is the library's key of its segment**: the
statement of cornerKeyIsTheLibrarysSegmentKey (…AtTheHeadA.lean), its binders to the letter, at key := .inl key. -/
theorem normCornerKeyIsTheLibrarysSegmentKey
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
    (key : FinalNorm.Key) (x t : Nat) (entryIsThere : x < lenOf (.inl key))
    (positionIsThere : t < 1024) :
    letI : Token := ⟨replyToken⟩
    rd (cornerKey (P5J.listCells publicPart.hS publicPart.HLy
        (OnBytes.Model.Verify.borderOf publicPart.y) matrices index.mat) (.inl key) x t) =
      OnBytes.Ends.H.segH (headPub publicPart coveredPositions checkedTokens)
        (OnBytes.Road.Hd.readH matrices index.mat) (segmentName (.inl key)) x t := by
  obtain ⟨lettersSame, lettersWide, -⟩ :=
    lettersAtTheHead inScope filesRead publicPartMade sizesAreThePublicParts replyToken
  have ties := librarysTiesAtTheHead inScope filesRead publicPartMade sizesAreThePublicParts
    requestIsOk replyToken replyTokenIsInTheVocabulary coveredPositions checkedTokens
    coveredPositionsAreTheRequests positionsWithCostAreTheRequests checkedTokensAreTheRequests
    replyTokenIsTheCheckedOne matrices index.mat
  have shift : FinalNorm.KF = (OnBytes.Road.Hd.npOf publicPart.hS).K := by
    subst sizesAreThePublicParts
    rfl
  letI : Token := ⟨replyToken⟩
  exact normKeyIsTheLibrarysSegmentKeyUnderTies
    (cells := P5J.listCells publicPart.hS publicPart.HLy
      (OnBytes.Model.Verify.borderOf publicPart.y) matrices index.mat)
    (headWeights := (Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef
      index.mat).H)
    ties lettersSame.T lettersWide.d
    (Nat.dvd_of_mod_eq_zero (VerifiableInference.Desc.Kinds.Head.Law.planFacts planIsOk).hdS)
    shift key x t entryIsThere positionIsThere

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.normKeyIsTheLibrarysSegmentKeyUnderTies
#print axioms ProofFile.Honest.K3.Term.normCornerKeyIsTheLibrarysSegmentKey
