-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Front/LiveBehindStatement.lean: BEHIND A YES OF THE MERGE's MEMBER FROM A STATE
THAT IS REACHED AT BORDER 346 THE CONDITION `MergeLive` (Johnson/Desc/K11/Live/RunStatement.lean)
HOLDS AT WRITTEN NUMBERS: 18 column bits, first slot 3531, the slot of the claim's value: WHERE NONE
OF THE CHALLENGES THAT THE SUMCHECK's ROUNDS DREW READS AS 0: under the library's hypothesis on the
public files (`P5J.AtMgA`) at the full size: STATEMENTS ALONE: three definitions of propositions.
NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `SvBelowRaw`          at a state reached at 346, whatever own part a and hearing x it holds: x.sV
                        < a.F.next: the one premise on the state in front of `HeadMergeLiveBehind`
                        (Johnson/Desc/K11/Live/BehindStatement.lean)
  `NextAtRaw`           there: a.F.next = 3531, and the kind's layout has 18 column bits
  `MergeLiveBehindRaw`  where the member as it stands at its seat says yes from such a state to s'
                        on the rounds rs, and every element of `laterDraws rs` reads other than 0:
                        `MergeLive 18 3531 x.sV s'`

Limits. "Reached" and the yes are premises: that any state is reached, or that the member says yes,
is not said. THAT NO CHALLENGE READS AS 0 IS A PREMISE: how often one does is not said. The
hypothesis is a premise; it stands at the earlier hash: no example of it is shown here; the
library's `head_exists_at_name` (Johnson/P5J/HeadExistsAtName.lean) has one under four premises. AT
THE FULL SIZE's WRITTEN NUMBERS ALONE. Nothing on any property.
-/
import Johnson.Desc.K11.Front.CountStatement
import Johnson.Desc.K11.Live.BehindStatement
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Front
open OnBytes.Model (Reading)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (S HeadOwn)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.Desc.First.ForkMerge.Live (MergeLive laterDraws)

/-- The statement on the slot of the claim's value. Not proved here; a lemma's statement, none of
the library's goals. -/
def SvBelowRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (z : ProofFile.InstPub) (sF : S) (a : HeadOwn) (x : OnBytes.Model.Head.Heard),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    sF.here = .head a → a.x = some x → x.sV < a.F.next

/-- The statement on the two numbers. Not proved here; a lemma's statement, none of the library's
goals. -/
def NextAtRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF : S) (a : HeadOwn),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    sF.here = .head a → a.F.next = 3531 ∧ (K11.parOf Zp Bs.G₀).lay.lk = 18

/-- The statement behind the member's yes. Not proved here; a lemma's statement, none of the
library's goals. -/
def MergeLiveBehindRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF s' : S) (a : HeadOwn)
    (x : OnBytes.Model.Head.Heard) (name : String) (pl : Place) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (K11.parOf Zp Bs.G₀)) name pl).decide sF rs gs =
      .ok s' →
    sF.here = .head a → a.x = some x →
    (∀ e ∈ laterDraws rs, Reading.gl.val e ≠ 0) →
    MergeLive 18 3531 x.sV s'

end Johnson.Desc.First.ForkMerge.Front

#print axioms Johnson.Desc.First.ForkMerge.Front.SvBelowRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.NextAtRaw
#print axioms Johnson.Desc.First.ForkMerge.Front.MergeLiveBehindRaw
