-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/AcceptedByTies.lean: K13's SUB-PROTOCOL AT 355 IS ACCEPTED AT THE
THREAD OF THE FIRST CHAIN UNDER THE LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE, THE HEAD's ARM OF THE
FILLER's PARAMETER LAID BY THE HONEST SIDE's OWN TEXT OF THE HEAD's MERGE, AND THE LAW ON THE HEAD's
CLAIM HAD FROM FOUR TIES ALONG THE FOLD OVER THE CHAIN's OWN LIST. One definition with code, and
statements with their proofs: calls.

`k13_accepted_at_head_text` (ClaimsText.lean of this folder) takes headArm as a parameter and hhead
(`HeadClaimIs`, Johnson/Desc/K13/Honest/ClaimsIsAt.lean, at cF.blocksInOrder, number 346) as a premise.
Honest/K11/ClaimBare.lean shows `HeadClaimIs` at that very list, by its name: `headClaimIsAtBare`:
where the arm is `headMergeClaims` (Honest/K11/Claims.lean) as an array, from `FourTies`
(Honest/K11/ClaimOfQuietStatement.lean) at every state without a mark, with the asked reply heard,
that the fold over the first 346 sub-protocols returns. It is called here.
Main names:
  `headArmOf H4 Z Bs`: **the head's arm**: of the instance x and the challenges hd: `some
    (headMergeClaims H4 Z Bs.G₀ x hd).toArray`. H4: the four parameters of Claims.lean
    (`HeadHeardFour`: what the head heard, as far as the claim reads it: the calls' key points; the
    challenges over positions and over channels; the tokens checked): a parameter here; a text for
    it: `headFourOfK6` (Honest/K11/ThreeTiesStatement.lean) at `headKeysOfK3`
    (Honest/K3/Law/Thread/HeadCallsTie.lean): PileIsAtHead.lean of this folder lays it. Where that
    text yields no claim the arm is the empty array, never nothing.
  `base_at_head`: under h there is a Bs with `ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok
    Bs` (the library's `IM.Open.made`, Johnson/IMR/SeatOpen.lean); being an equation of a function's
    value it has at most one. The equation stands in the statement below as hB: hH and hties name
    Bs, and under h alone Bs is no term.
  `k13_accepted_at_head_ties`: **`AcceptedS` at 355, at every Said**, from: h · hB · b₀ ≤ 355 · hH
    (the honest part found at the place of number 355 is `proverSideOfClaimCombination` at the filler over `claimsText cF
    Zp lookOf (headArmOf H4 Zp Bs) Q₀`) · htie (in lookOf) · hties (`FourTies` along the fold). htie
    and hties are asked at every returning fold over cF.blocksInOrder: the list at which the thread's own
    clause on the fold stands. No premise on the thread.

What is not claimed. hH, htie, hties; that they can be met together. No text for lookOf or for H4 is
laid here (PileIsAtHead.lean lays `lookOfK3` and `headFourOfK6`, and calls the payers of the like
premises). `AcceptedS` (Honest/Thread/PaysS.lean) is itself a premise's form: IF the thread and Said
stand in front, the challenges fit, nothing stops, `fall` is silent and the member has moved, THEN
the sub-protocol's step returns: where the thread stands nowhere it speaks of nothing.
`k13_accepted_at_head_ties` is called by no file of the library yet: `AcceptedS` at 355 is a debt of
the kind, and the files that would call it are no part of the library; the four statements of this
folder that end in `AcceptedS` (AcceptedAtHeadK4.lean, K4PubsTerm.lean, ClaimsText.lean, this file)
call each the one before, and serve none of `k13_pileIs_at_head`, `k13_g_at_356_pileAnyK3`,
`k13_pileOneS_at_356`: of these four files the later ones use the definitions and three small
statements (`k4PubsAt_term`, `claimsText_arm`, `claimsText_head`). `base_at_head`
is named by two heads as the reason why hB can be met, and called by nothing. That h holds at any
public files. Q₀: a free parameter: three fields that no line here reads. It is none of the
library's goals. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ClaimsText
import Johnson.Desc.ProofFile.Honest.K11.ClaimBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (Chain Strs Place foldBlocks)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open ProofFile.Honest.K11 (HeadHeardFour headMergeClaims FourTies headClaimIsAtBare)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)

/-- **The head's arm of the filler's parameter**: the honest side's own text of the claims that the
head's merge merges, as an array. H4: that text's four parameters. -/
def headArmOf (H4 : ProofFile.Pub → ProofFile.Ground → HeadHeardFour) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) :
    ProofFile.Inst → List Fmt.Drawn → Option (Array WsClaim) :=
  fun x hd => some (headMergeClaims H4 Z Bs.G₀ x hd).toArray

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

include h in
/-- Under h the maker's base returns. -/
theorem base_at_head : ∃ Bs, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨Bs, O.made⟩

/-- **K13's SUB-PROTOCOL AT 355 IS ACCEPTED**, the law on the head's claim had from the four ties
along the fold over the chain's own list. -/
theorem k13_accepted_at_head_ties
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {weights : W₀ → Weights} (hb : b₀ ≤ 355)
    (lookOf : Nat → ProofFile.Inst → List Fmt.Drawn → Forest.Heard)
    (H4 : ProofFile.Pub → ProofFile.Ground → HeadHeardFour) (Bs : ProofFile.PureBase)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (Q₀ : Nat → K4Pub)
    (hH : ∀ blk, cF.blocksInOrder[355]? = some blk →
      (H.first.find? fun g => g.place == blk.place) =
        some (proverSideOfClaimCombination weights
          (fillerAt cF Zp (claimsText cF Zp lookOf (headArmOf H4 Zp Bs) Q₀)) h.𝔇.P13))
    (htie : ∀ g < 12, ∀ (ξ : ProofFile.Inst) rs cols sj c y fo,
      foldBlocks 0 (cF.blocksInOrder.take (28 * g + 4)) (ProofFile.startS Zp ξ.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder (28 * g + 4)), c) →
      sj.failed = none → sj.here = .lay y → y.fo = some fo →
      (lookOf g ξ ((rs.take (roundsAhead cF.blocksInOrder (28 * g + 4))).map (·.drawn))).zk = fo.zk)
    (hties : ∀ (ξ : ProofFile.Inst) rs cols sj c,
      foldBlocks 0 (cF.blocksInOrder.take 346) (ProofFile.startS Zp ξ.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead cF.blocksInOrder 346), c) →
      sj.failed = none → sj.out.reply = some ξ.asked →
      FourTies (H4 Zp Bs.G₀) ξ ((rs.take (roundsAhead cF.blocksInOrder 346)).map (·.drawn)) sj)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall 355 :=
  k13_accepted_at_head_text h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hb lookOf
    (headArmOf H4 Zp Bs) Q₀ hH htie
    (headClaimIsAtBare H4 Z D r Zp Np cF x Bs 24 (fun _ => headArmOf H4 Zp Bs) h hB
      (fun _ _ => rfl) hties)
    fall

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.base_at_head
#print axioms ProofFile.Honest.K13.k13_accepted_at_head_ties
#print axioms ProofFile.Honest.K13.headArmOf
