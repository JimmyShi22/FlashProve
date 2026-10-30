-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ThreeTiesBareStatement.lean: `ThreeTiesAlongFold` AND
`HeadClaimIsOfKeys` (ThreeTiesStatement.lean of this folder) AT THE FIRST CHAIN's OWN FLAT LIST,
BARE: THE LIST THAT RUNS: STATEMENTS ALONE: two definitions of propositions, made by program of
those two: cF.blocksInOrder for cF.blocksInOrder.map below at all places. NOTHING IS PROVED IN THIS FILE, and neither
is one of the library's goals: they are lemmas' statements.

  `ThreeTiesAlongBareFold`   under the library's one hypothesis at the full size: at every state
                             without a mark, with the asked reply heard, that the fold over the
                             first 346 sub-protocols of cF.blocksInOrder returns: what the head heard there
                             has the three fields of `headFourOfK6`, at the list of what the rounds
                             in front drew
  `HeadClaimIsOfKeysBare`    `HeadClaimIs` at cF.blocksInOrder, number 346, from the one tie that is left:
                             each call's key point

Limits. THE TIE ON THE KEY POINTS IS A PREMISE: it is the lookup's on the head's calls. The
hypothesis is a premise; it stands at the earlier hash. That a fold returns anywhere is not said.
THE PROOFS (ThreeTiesBare.lean of this folder) STAND OVER ANOTHER GROUP OF AUTHORS'
Johnson/Desc/ProofFile/Honest/K6/HeardAtYes.lean and what lies beneath it. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.AtZ (rqAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.K13.Honest (SiteClaims HeadClaimIs roundsAhead)
open ProofFile.Honest.K6 (headTHr headRs headWin)

/-- The statement on the three. Not proved here; a lemma's statement, none of the library's goals.
-/
def ThreeTiesAlongBareFold : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    ∀ (x : Inst) rs cols sj c,
      foldBlocks 0 (cF.blocksInOrder.take 346) (ProofFile.startS Zp x.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder 346), c) →
      sj.failed = none → sj.out.reply = some x.asked →
      ∀ a hx, sj.here = .head a → a.x = some hx →
        hx.tH.r = headTHr (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
            (roundsAhead cF.blocksInOrder 341)
            ((rs.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn)) ∧
          hx.rs = headRs (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
            (roundsAhead cF.blocksInOrder 341)
            ((rs.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn)) ∧
          hx.win = headWin (parOf Bs.G₀.W.hS (workOf Bs.G₀.W))
            (rqAt Zp x.pub) (OnBytes.Desc.Reply.tokOf x.asked)

/-- The statement from the one tie. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadClaimIsOfKeysBare : Prop :=
  ∀ (keys : Pub → Ground → List Fmt.Drawn → Array (Array E)) (Z : VerifierAndGoals.PublicFiles)
    (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase)
    (link : Nat) (claims : SiteClaims Inst),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ x hd, claims link x hd = some (headMergeClaims
      (headFourOfK6 keys (roundsAhead cF.blocksInOrder 341)) Zp Bs.G₀ x hd).toArray) →
    (∀ (x : Inst) rs cols sj c,
      foldBlocks 0 (cF.blocksInOrder.take 346) (ProofFile.startS Zp x.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder 346), c) →
      sj.failed = none → sj.out.reply = some x.asked →
      ∀ a hx, sj.here = .head a → a.x = some hx →
        hx.g1.zk = keys Zp Bs.G₀
          ((rs.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn))) →
    HeadClaimIs cF.blocksInOrder (fun x : Inst => ProofFile.startS Zp x.pub) 346 link claims
      (fun x => x.asked)

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.ThreeTiesAlongBareFold
#print axioms ProofFile.Honest.K11.HeadClaimIsOfKeysBare
