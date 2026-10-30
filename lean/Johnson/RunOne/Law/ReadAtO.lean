-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/ReadAtO.lean: It stands on Johnson/RunOne/Sound/.
THE LINKS' PUBLIC PREMISES AND THE PROMISE IN FRONT OF THE FIRST LINK, AT
THE ROUTINE BY WHICH THE VERIFIER'S TEXT READS THE PUBLIC FILES: publicOfO o
(Johnson/Desc/Ok/PlanWritten/PublicAt.lean), which takes the hash function as a letter o: at every
o.

AtFreeCfg.lean and FrontAtFK.lean ask ReadOf pol Z of what was read. publicOfO o pays it, by the
steps by which the program's own publicOf does (publicOf_wsLay,
Johnson/Goal/PlanValues/ScopeAtPlan.lean): the two texts part in the hash function alone.

Main names (readOf_publicOfO: ReadOf, from publicOfO o's yes, at every o: has moved, under its full
name, to KeyInScope.lean):
  seat_at_o, front_at_o: seat_at_fixed and front_at_fixed from the yes of
    (publicOfO o pol KL (some lay)).bind fun Z => Key.keyDataAndDecisionAtFixedDigest Z lay.

Object: that term: by what is told of the verifier's text it is the value of the
key file's slot at the letter o; that text is not imported here, so this is not held by Lean.
User: none yet.
Letters: Zp: three public files in scope · o: ANY function in the hash function's place.

Limits. Those of AtFreeCfg.lean and FrontAtFK.lean. Nothing on soundness.

-/
import Johnson.RunOne.Law.FrontAtFK
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.ReadAtO
open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open Lk6.AtPlan
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim keyDataAndDecisionAtFixedDigest KeyRun)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.AtFreeCfg
open Johnson.RunOne.Law.FrontSteps
open Johnson.RunOne.Law.FrontAtFK

/-- **The three public premises of the links' laws, in scope, at every letter o.** -/
theorem seat_at_o {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {o : Nat → ByteArray → ByteArray} {D : OnBytes.Maker.WholeD} {r : KeyRun}
    (h : ((publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z Zp.lay) =
      .ok (D, r)) :
    ∃ X N P, (FK X N P).planOk = true ∧ (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧ X.set.target = 128 ∧
      (∀ l, l < X.Y.k.oneTime.ranges.lookups.length →
        LookHeld X.set (faceOfLkp (Wf.lookupOf X.Y.k.oneTime.ranges.messageId
          (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime l)))) ∧
      RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
        X.Y.k.oneTime.indexMasks.shape := by
  obtain ⟨Z, hP, hl⟩ := exc_bind h
  exact seat_at_fixed hZ (readOf_publicOfO hP) hl

/-- **The promise in front of the first link, in scope, at every letter o.** -/
theorem front_at_o {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {o : Nat → ByteArray → ByteArray} {D : OnBytes.Maker.WholeD} {r : KeyRun}
    (h : ((publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z => keyDataAndDecisionAtFixedDigest Z Zp.lay) =
      .ok (D, r)) :
    ∃ X N P, (FK X N P).planOk = true ∧ (FK X N P).data "key file" = .ok D ∧
      r = (FK X N P).run ∧
      (∀ (b : Block FirstState Claim) (q : (FK X N P).XiPub) (t : FirstState) (r₁ r₂ : Fmt.RoundView)
        (gs : List (List (ℕ × List UInt64))), (FK X N P).first.blocksInOrder[0]? = some b →
        b.decide ((FK X N P).start₁ q) [r₁, r₂] gs = .ok t → Half X.Y.k.oneTime t) ∧
      (∀ (b : Block FirstState Claim) (s t : FirstState) (r₁ r₂ : Fmt.RoundView)
        (gs : List (List (ℕ × List UInt64))), (FK X N P).first.blocksInOrder[1]? = some b →
        Half X.Y.k.oneTime s → b.decide s [r₁, r₂] gs = .ok t → Front X.Y.k.oneTime t) ∧
      ∀ (Ex : FirstState → Prop) (t : FirstState), Front X.Y.k.oneTime t → Ex t →
        t.base.rows.length = 0 ∧ t.base.keys.length = 0 ∧
          PromL X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
            (Lof X.Y.k.oneTime) 0 X.Y.k.oneTime.ranges.lookups.length
            (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
            (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) Ex 0 t := by
  obtain ⟨Z, hP, hl⟩ := exc_bind h
  exact front_at_fixed hZ (readOf_publicOfO hP) hl

end Johnson.RunOne.Law.ReadAtO

#print axioms Johnson.RunOne.Law.ReadAtO.seat_at_o
#print axioms Johnson.RunOne.Law.ReadAtO.front_at_o
