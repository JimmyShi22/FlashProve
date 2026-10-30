-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimBareStatement.lean: THE LAW ON THE HEAD's CLAIM
(`HeadClaimIs`, Johnson/Desc/K13/Honest/ClaimsIsAt.lean) AT THE FIRST CHAIN's OWN FLAT LIST, BARE:
THE LIST THAT RUNS: NO TEST ON THE SHOWN WORDS IN FRONT OF A SUB-PROTOCOL: under the library's one
hypothesis, from the four ties along that list's fold: STATEMENTS ALONE: three definitions of
propositions. NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are
lemmas' statements.

Why. `HeadClaimIsAtHead` (ClaimIsStatement.lean of this folder) stands at the list with that test in
front of each sub-protocol, because it goes by the library's condition on the state in front of the
merge (`WaK6`, Johnson/Desc/Kinds/Law/WtJointAt.lean), which the library has at that list's
"reached" alone. Of that condition's seven clauses the law on the claim spends four; the one that
wants the test ("the rounds of the output head's yes are canonical") it does not spend.

  `FrontOfMergeRaw`     at every state sF that is reached at border 346 BY THE SUB-PROTOCOLS' OWN
                        STEPS (`Reach` over cF.blocksInOrder, Johnson/Top/H0/Walk/Reach.lean): a yes of the
                        output head's own block from some s to some s' · sF goes on from s' as far
                        as the library's sentence reads (`KeptW`) · the covered positions are had at
                        sF · the claim that lies at sF, if one lies there, is what the description's
                        function makes
  `HeadClaimAskedRaw`   `HeadClaimAsked` (ClaimAskedStatement.lean of this folder) with that
                        "reached" for the library's
  `HeadClaimIsAtBare`   `HeadClaimIsAtHead`'s text with cF.blocksInOrder for cF.blocksInOrder.map below, at all its
                        places

Limits. THE FOUR TIES ARE A PREMISE. The hypothesis is a premise; it stands at the earlier hash.
That a fold returns anywhere is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimIsStatement
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head (blockAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf KeptW runAt)
open VerifiableInference.Desc.K13.Honest (SiteClaims HeadClaimIs roundsAhead)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- The statement on the state in front of the merge. Not proved here; a lemma's statement, none of
the library's goals. -/
def FrontOfMergeRaw : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase) (z : ProofFile.InstPub) (sF : S),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, sF) →
    ∃ (s s' : S) (rv : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (cov : Head.Covered)
      (t : Head.Tables),
      (blockAt Bs.G₀.W.hS (VerifiableInference.Desc.Kinds.Head.Law.readsOf Bs.G₀.W)
        (workOf Bs.G₀.W) 24).decide s rv gs = .ok s' ∧
      KeptW s' sF ∧ sF.covered Bs.G₀.W.T Bs.G₀.W.P.h.V = .ok cov ∧
      ∀ o' x claim, sF.here = .head o' → o'.x = some x → o'.claim = some claim →
        VerifiableInference.Desc.First.Look.weightsClaim (runAt Bs.G₀.W cov x t)
          Bs.G₀.W.layers.wsLay = .ok claim

/-- The statement at border 346. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadClaimAskedRaw : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase)
    (x : Inst) (heard : List Fmt.Drawn) (s : S) (o : HeadOwn) (claim : WsClaim),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (x.pub, s) →
    s.failed = none → s.out.reply = some x.asked →
    s.here = .head o → o.claim = some claim →
    FourTies (H Zp Bs.G₀) x heard s →
    headMergeClaims H Zp Bs.G₀ x heard = [claim]

/-- The statement at the bare list. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadClaimIsAtBare : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase) (link : Nat)
    (claims : SiteClaims Inst),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ x hd, claims link x hd = some (headMergeClaims H Zp Bs.G₀ x hd).toArray) →
    (∀ (x : Inst) rs cols sj c,
      foldBlocks 0 (cF.blocksInOrder.take 346) (ProofFile.startS Zp x.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder 346), c) →
      sj.failed = none → sj.out.reply = some x.asked →
      FourTies (H Zp Bs.G₀) x ((rs.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn)) sj) →
    HeadClaimIs cF.blocksInOrder (fun x : Inst => ProofFile.startS Zp x.pub) 346 link claims (fun x => x.asked)

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.FrontOfMergeRaw
#print axioms ProofFile.Honest.K11.HeadClaimAskedRaw
#print axioms ProofFile.Honest.K11.HeadClaimIsAtBare
