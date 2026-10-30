-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimOfQuietStatement.lean: THE CLAIM THAT THE VERIFIER's QUIET
STEP IN FRONT OF THE MERGE's MEMBER LAYS IS THE ONE THAT THE HONEST SIDE's TEXT MAKES, UNDER FOUR
TIES ON WHAT THE HEAD HEARD: STATEMENTS ALONE: three definitions of propositions. NOTHING IS PROVED
IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

The verifier's text: `K3.quietHead X s` (Johnson/Desc/First/Look/K3Whole.lean) lays the head's one
claim on the weights. The library says which (`K3.quietHead_claim`,
Johnson/Desc/First/Look/K3QuietLaws.lean): `weightsClaim` at a run made of the public data, the
covered positions, and what the head heard. The honest side's text: `headMergeClaims H Z G x heard`
(Honest/K11/Claims.lean): the same function at a run made of the public data, the instance, and four
parameters that are still open (`HeadHeardFour`).

  `FourTies H x heard s`   where s stands in the head's link and what the head heard is laid: its
                           four fields that `weightsClaim` reads are the four parameters' values:
                           each call's key point · the challenges over the positions · those over
                           the channels · the checked tokens
  `HeadClaimOfRun`         THE CORE, WITH NO STEP: where `S.covered` answers cov at s, and
                           `weightsClaim` yields a claim at the run made of the ground's public
                           data, cov, a hearing hx and any tables; the request's words in s are
                           those of the description's first state; the token that is asked about is
                           an entry of the vocabulary; and hx's four fields are the four
                           parameters' values: THE TEXT YIELDS JUST THAT CLAIM
  `HeadClaimOfQuiet`       where the quiet step returns t at s, at the ground's public data; the
                           request's words in s are those of the description's first state; the
                           token that is asked about is an entry of the vocabulary; and the four
                           ties hold at s: t stands in the head's link with a claim laid, and THE
                           TEXT YIELDS JUST THAT CLAIM

Limits. THE FOUR TIES ARE A PREMISE: nothing here says what the kinds whose rounds draw these
challenges lay, and the four parameters stay open. That the quiet step returns is a premise; so is
the tie on the request's words. The public data are the ground's (G.W); the lookups' lot lays the
quiet step at Z.p.X: that the two are one is not said here. Of the heard reply nothing is asked: the
claim reads of the covered positions only which are covered, which the words alone say. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Claims
import Johnson.Desc.First.Look.K3Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (weightsClaim)
open VerifiableInference.Desc.K3 (quietHead)

/-- The four ties, at a state. -/
def FourTies (H : HeadHeardFour) (x : Inst) (heard : List Fmt.Drawn) (s : S) : Prop :=
  ∀ a hx, s.here = .head a → a.x = some hx →
    hx.g1.zk = H.keys heard ∧ hx.tH.r = H.overPositions heard ∧ hx.rs = H.overChannels heard ∧
      hx.win = H.checked x

/-- The statement of the core. cov: the covered positions as the state's own reader makes them. hx:
a hearing. t': any tables. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadClaimOfRun : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : Pub) (G : Ground) (x : Inst) (heard : List Fmt.Drawn)
    (s : S) (cov : Head.Covered) (hx : Head.Heard) (t' : Head.Tables) (claim : WsClaim),
    s.covered G.W.T G.W.P.h.V = .ok cov →
    weightsClaim
      { h := G.W.hS, L := G.W.HLy, b := Verify.borderOf G.W.y, hp := G.W.H, cov := cov, x := hx
        t := t', iU3 := (G.W.H.tl.ix.U.getD 2 none).getD 0 } G.W.layers.wsLay = .ok claim →
    s.req = (startS Z x.pub).req →
    ((Verify.words32 x.y).getD 0 0).toNat < G.W.P.h.V →
    hx.g1.zk = (H Z G).keys heard → hx.tH.r = (H Z G).overPositions heard →
    hx.rs = (H Z G).overChannels heard → hx.win = (H Z G).checked x →
    headMergeClaims H Z G x heard = [claim]

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadClaimOfQuiet : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : Pub) (G : Ground) (x : Inst) (heard : List Fmt.Drawn)
    (s t : S),
    quietHead G.W s = .ok t →
    s.req = (startS Z x.pub).req →
    ((Verify.words32 x.y).getD 0 0).toNat < G.W.P.h.V →
    FourTies (H Z G) x heard s →
    ∃ a claim, t.here = .head a ∧ a.claim = some claim ∧ headMergeClaims H Z G x heard = [claim]

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.FourTies
#print axioms ProofFile.Honest.K11.HeadClaimOfRun
#print axioms ProofFile.Honest.K11.HeadClaimOfQuiet
