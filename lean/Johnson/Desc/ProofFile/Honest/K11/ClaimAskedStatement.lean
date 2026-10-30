-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimAskedStatement.lean: THE CLAIM IN FRONT OF THE MERGE's
MEMBER, WHERE THE REPLY THAT WAS HEARD IS THE ONE THAT IS ASKED ABOUT: STATEMENTS ALONE: two
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the library's
goals: they are lemmas' statements.

  `AskedSmallOfReply`    where the state holds the instance's asked reply as heard, and `S.covered`
                         answers at a vocabulary of V entries: the token that is asked about is
                         below V
  `HeadClaimAsked`       `HeadClaimReached` (ClaimAtHeadStatement.lean of this folder) with "the
                         state holds the asked reply as heard" in the place of "the asked token is
                         an entry of the vocabulary"

Limits. Those of ClaimAtHeadStatement.lean: THE FOUR TIES ARE A PREMISE; that a claim is laid is a
premise; the hypothesis is a premise. That the heard reply is the asked one is a premise. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimAtHeadStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.Walk.Tied (RchAt)

/-- The statement on the asked token. Not proved here; a lemma's statement, none of the library's
goals. -/
def AskedSmallOfReply : Prop :=
  ∀ (x : Inst) (s : S) (T V : Nat) (cov : Head.Covered),
    s.out.reply = some x.asked → s.covered T V = .ok cov →
    ((Verify.words32 x.y).getD 0 0).toNat < V

/-- The statement at border 346. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadClaimAsked : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase) (Str : Type) (y : Str)
    (x : Inst) (heard : List Fmt.Drawn) (s : S) (o : HeadOwn) (claim : WsClaim),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 346 ((x.pub, s), y) →
    s.failed = none → s.out.reply = some x.asked →
    s.here = .head o → o.claim = some claim →
    FourTies (H Zp Bs.G₀) x heard s →
    headMergeClaims H Zp Bs.G₀ x heard = [claim]

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.AskedSmallOfReply
#print axioms ProofFile.Honest.K11.HeadClaimAsked
