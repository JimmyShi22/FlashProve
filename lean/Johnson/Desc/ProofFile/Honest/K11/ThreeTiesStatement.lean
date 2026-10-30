-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ThreeTiesStatement.lean: THREE OF THE FOUR TIES ON WHAT THE HEAD
HEARD (`FourTies`, ClaimOfQuietStatement.lean of this folder), ALONG THE FOLD OVER THE FIRST 346
SUB-PROTOCOLS OF THE FIRST CHAIN's LIST, AT WRITTEN FUNCTIONS OF THE CHALLENGES AND THE INSTANCE;
AND THE LAW ON THE HEAD's CLAIM (`HeadClaimIs`, Johnson/Desc/K13/Honest/ClaimsIsAt.lean) FROM ONE
TIE: A DEFINITION AND STATEMENTS: NOTHING IS PROVED IN THIS FILE, and none is one of the library's
goals: they are lemmas' statements.

  `headFourOfK6`         the four parameters of Claims.lean of this folder with three filled: the
                         challenges over the positions and over the channels, and the checked
                         tokens, are the output head's honest side's own functions (`headTHr`,
                         `headRs`, `headWin`, Johnson/Desc/ProofFile/Honest/K6/Heard.lean) at the
                         head's public numbers, the number n of rounds in front of the output head's
                         own sub-protocol, the request that the instance's words spell (`rqAt`,
                         Johnson/Desc/Kinds/Head/AtZ.lean), and the asked token; each call's key
                         point stays a letter
  `ThreeTiesAlongFold`   under the library's one hypothesis at the full size: at every state without
                         a mark, with the asked reply heard, that the fold over the first 346
                         returns: what the head heard there has these three fields, at the list of
                         what the rounds in front drew
  `HeadClaimIsOfKeys`    `HeadClaimIs` at that list, number 346, from the one tie that is left: each
                         call's key point

THE LIST IS THE FIRST CHAIN's FLAT LIST WITH EACH SUB-PROTOCOL BEHIND THE TEST THAT EVERY WORD SHOWN
IS BELOW THE PRIME: as in ClaimIsStatement.lean of this folder: IT IS NOT THE LIST THAT RUNS.

Limits. THE TIE ON THE KEY POINTS IS A PREMISE: it is the lookup's on the head's calls. The
hypothesis is a premise; it stands at the earlier hash. That a fold returns anywhere is not said.
THE PROOFS (ThreeTies.lean of this folder) STAND OVER ANOTHER GROUP OF AUTHORS'
Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean and what lies beneath it. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimIsStatement
import Johnson.Desc.ProofFile.Honest.K6.Heard
import Johnson.Desc.Kinds.Head.AtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.AtZ (rqAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.K13.Honest (SiteClaims HeadClaimIs roundsAhead)
open ProofFile.Honest.K6 (headTHr headRs headWin)

/-- The four parameters with three filled. keys: each call's key point. n: the number of rounds in
front of the output head's own sub-protocol. -/
def headFourOfK6 (keys : Pub → Ground → List Fmt.Drawn → Array (Array E)) (n : Nat) (Z : Pub)
    (G : Ground) : HeadHeardFour :=
  { keys := keys Z G
    overPositions := headTHr (parOf G.W.hS (workOf G.W)) n
    overChannels := headRs (parOf G.W.hS (workOf G.W)) n
    checked := fun x => headWin (parOf G.W.hS (workOf G.W)) (rqAt Z x.pub)
      (OnBytes.Desc.Reply.tokOf x.asked) }

/-- The statement on the three. Not proved here; a lemma's statement, none of the library's goals.
-/
def ThreeTiesAlongFold : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ∀ (x : Inst) rs cols sj c,
      foldBlocks 0 ((cF.blocksInOrder.map below).take 346) (ProofFile.startS Zp x.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead (cF.blocksInOrder.map below) 346), c) →
      sj.failed = none → sj.out.reply = some x.asked →
      ∀ a hx, sj.here = .head a → a.x = some hx →
        hx.tH.r = headTHr (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
            (roundsAhead (cF.blocksInOrder.map below) 341)
            ((rs.take (roundsAhead (cF.blocksInOrder.map below) 346)).map (·.drawn)) ∧
          hx.rs = headRs (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
            (roundsAhead (cF.blocksInOrder.map below) 341)
            ((rs.take (roundsAhead (cF.blocksInOrder.map below) 346)).map (·.drawn)) ∧
          hx.win = headWin (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
            (rqAt Zp x.pub) (OnBytes.Desc.Reply.tokOf x.asked)

/-- The statement from the one tie. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadClaimIsOfKeys : Prop :=
  ∀ (keys : Pub → Ground → List Fmt.Drawn → Array (Array E)) (Z : VerifierAndGoals.PublicFiles)
    (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase)
    (link : Nat) (claims : SiteClaims Inst),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ x hd, claims link x hd = some (headMergeClaims
      (headFourOfK6 keys (roundsAhead (cF.blocksInOrder.map below) 341)) Zp Bs.G₀ x hd).toArray) →
    (∀ (x : Inst) rs cols sj c,
      foldBlocks 0 ((cF.blocksInOrder.map below).take 346) (ProofFile.startS Zp x.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead (cF.blocksInOrder.map below) 346), c) →
      sj.failed = none → sj.out.reply = some x.asked →
      ∀ a hx, sj.here = .head a → a.x = some hx →
        hx.g1.zk = keys Zp Bs.G₀
          ((rs.take (roundsAhead (cF.blocksInOrder.map below) 346)).map (·.drawn))) →
    HeadClaimIs (cF.blocksInOrder.map below) (fun x : Inst => ProofFile.startS Zp x.pub) 346 link claims
      (fun x => x.asked)

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headFourOfK6
#print axioms ProofFile.Honest.K11.ThreeTiesAlongFold
#print axioms ProofFile.Honest.K11.HeadClaimIsOfKeys
