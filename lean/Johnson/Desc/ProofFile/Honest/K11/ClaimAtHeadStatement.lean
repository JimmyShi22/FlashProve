-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimAtHeadStatement.lean: THE CLAIM THAT LIES IN THE VERIFIER's
STATE IN FRONT OF THE MERGE's MEMBER IS THE ONE THAT THE HONEST SIDE's TEXT MAKES, UNDER FOUR TIES
ON WHAT THE HEAD HEARD: AT THE LIBRARY's OWN CONDITION ON THAT STATE, AND AT EVERY STATE WITHOUT A
MARK THAT IS REACHED AT BORDER 346 UNDER THE LIBRARY's ONE HYPOTHESIS: STATEMENTS ALONE: three
definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's
goals: they are lemmas' statements.

  `HeardLaidOfWa`       where the library's condition on the state in front of the merge holds at s
                        (`WaK6`, Johnson/Desc/Kinds/Law/WtJointAt.lean): s stands in the head's
                        link, and what the head heard is laid
  `HeadClaimOfWa`       where that condition holds at s, at the ground's public data (four of its
                        clauses are spent: the output head's own rounds were accepted; what lies
                        between has kept the hearing; the covered positions are read; the claim
                        that lies in the state is the one that `weightsClaim` makes); s stands in
                        the head's link with a claim laid; the request's words in s
                        are those of the description's first state; the token that is asked about
                        is an entry of the vocabulary; and the four ties hold at s (`FourTies`,
                        ClaimOfQuietStatement.lean of this folder): THE TEXT YIELDS JUST THAT CLAIM
  `HeadClaimReached`    under the library's one hypothesis at the full size; Bs: what the maker's
                        base returns; s: a state without a mark that is reached at border 346, in
                        front of the merge's member, from the instance's public half; with a
                        claim laid; the asked token an entry of the vocabulary; the four ties: THE
                        TEXT, AT THE HYPOTHESIS's PUBLIC PART AND Bs's GROUND, YIELDS JUST THAT
                        CLAIM. NOTHING IS ASKED ON THE REQUEST's WORDS, ON THE QUIET STEP, ON WHICH
                        PUBLIC DATA IT WAS LAID AT, OR THAT A HEARING IS LAID

Limits. THE FOUR TIES ARE A PREMISE: nothing here says what the kinds whose rounds draw these
challenges lay, and the four parameters of Claims.lean stay open. That a claim is laid in the
state is a premise. The hypothesis is a premise; it stands at the earlier hash. No state is shown to
be reached. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimOfQuietStatement
import Johnson.Desc.Kinds.Law.WtJointAt
import Johnson.P5J.MgAtAll
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6)
open Johnson.Desc.First.Walk.Tied (RchAt)

/-- The statement that a hearing is laid. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeardLaidOfWa : Prop :=
  ∀ (W : Verify.Public) (V' : Nat) (s : S), WaK6 W V' s →
    ∃ (o : HeadOwn) (hx : Head.Heard), s.here = .head o ∧ o.x = some hx

/-- The statement at the library's condition. Not proved here; a lemma's statement, none of the
library's goals. -/
def HeadClaimOfWa : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : Pub) (G : Ground) (x : Inst) (heard : List Fmt.Drawn)
    (s : S) (o : HeadOwn) (claim : WsClaim),
    WaK6 G.W G.W.P.h.V s →
    s.here = .head o → o.claim = some claim →
    s.req = (startS Z x.pub).req →
    ((Verify.words32 x.y).getD 0 0).toNat < G.W.P.h.V →
    FourTies (H Z G) x heard s →
    headMergeClaims H Z G x heard = [claim]

/-- The statement at border 346. Str, y: whatever stands beside the statement's first half: not
read. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadClaimReached : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase) (Str : Type) (y : Str)
    (x : Inst) (heard : List Fmt.Drawn) (s : S) (o : HeadOwn) (claim : WsClaim),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    RchAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 346 ((x.pub, s), y) →
    s.failed = none → s.here = .head o → o.claim = some claim →
    ((Verify.words32 x.y).getD 0 0).toNat < Bs.G₀.W.P.h.V →
    FourTies (H Zp Bs.G₀) x heard s →
    headMergeClaims H Zp Bs.G₀ x heard = [claim]

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.HeardLaidOfWa
#print axioms ProofFile.Honest.K11.HeadClaimOfWa
#print axioms ProofFile.Honest.K11.HeadClaimReached
