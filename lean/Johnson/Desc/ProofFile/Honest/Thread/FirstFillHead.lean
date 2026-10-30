-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillHead.lean: CONDITIONAL: UNDER THE LIBRARY's HEAD:
WHICH PROVER's SIDE STANDS AT THE PLACE OF THE FIRST CHAIN's MEMBERS NUMBER 338 (the next token,
kind K7) AND NUMBER 355 (the members' batching, kind K13) IN THE PROVER THAT onlineProverFromPublicFiles RETURNS AT THE
HEAD's THREE PUBLIC FILES AND THE FILLING widerFillAt. Statements with their proofs.

Why. k7_half_wider and k13_half_wider (Honest/Thread/FirstFillThree.lean) are general in the public
files, so their places and sides are terms over what onlineProverFromPublicFiles returns: ⟨1, some (A.G.built.size - 1),
1, .K7⟩, K13.k13Place (whereOf A.Z), A.G. A caller that comes with a member of the chain and the
head's own public part and ground needs them at these.

  k7_half_head     CONDITIONAL: **∀ blk, cF.blocksInOrder[338]? = some blk → A.H.first.find? (fun g =>
                   g.place == blk.place) = some (replyHalf 24 1 G.W.hS.V)**
  k13_half_head    CONDITIONAL: **∀ blk, cF.blocksInOrder[355]? = some blk → … = some (K13.proverSideOfClaimCombination
                   (I.weights Zp) (O.pile Zp G) (whereOf Zp))**

The premises. h: the library's head (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) · hG: G is the ground that
the maker makes of the head's public part · hA: onlineProverFromPublicFiles returns A at the head's three files and the
filling · K: WiderKinds at the head's public part and that ground.

THAT A's PUBLIC PART AND GROUND ARE THE HEAD's IS NOT PROVED HERE: it is atPure_at_laid_ground
(Honest/AtHeadGround.lean), called. Called beside it: place_of_member, built_25, ps_338, ps_355
(Honest/Thread/HeadFacts.lean) · K13.k13Place_whereOf (Honest/K13/LotKind.lean: the place of the
members' batching as numbers).

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. h is a hypothesis; that onlineProverFromPublicFiles returns there is a hypothesis; K is a hypothesis
here (it is the end of widerKinds, Honest/Thread/FirstFillAll.lean). That there is a ground G with
hG under h is not said here. Of the kinds K7 and K13 alone. At the library's full size and the
format's second hash function alone. The statements are about lists and places. No property of a prover or a
protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillThree
import Johnson.Desc.ProofFile.Honest.Thread.HeadFacts
import Johnson.Desc.ProofFile.Honest.AtHeadGround
import Johnson.P5J.MgAtAll
import Johnson.P5J.PlacesPaid
import Johnson.IMR.PureJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName Chain Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

variable {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {G : Ground}

include h in
/-- **THE SIDE THAT IS FOUND AT THE PLACE OF THE MEMBER NUMBER 338.** CONDITIONAL: under the
hypothesis h; G is the ground that is made of the head's public part; onlineProverFromPublicFiles returns A at the head's
three files and the filling; WiderKinds at the head's public part and G. -/
theorem k7_half_head (hG : blankBy pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O Zp G) :
    ∀ blk, cF.blocksInOrder[338]? = some blk →
      A.H.first.find? (fun g => g.place == blk.place) = some (replyHalf 24 1 G.W.hS.V) := by
  intro blk hb
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have ep : blk.place = ⟨1, some 24, 1, .K7⟩ :=
    Option.some.inj ((place_of_member h hb).symm.trans ps_338)
  have e := k7_half_wider hA (by rw [eZ, eG]; exact K)
  rw [eG, built_25 h hG] at e
  rw [ep]
  exact e

include h in
/-- **THE SIDE THAT IS FOUND AT THE PLACE OF THE MEMBER NUMBER 355.** CONDITIONAL: as at 338. -/
theorem k13_half_head (hG : blankBy pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O Zp G) :
    ∀ blk, cF.blocksInOrder[355]? = some blk →
      A.H.first.find? (fun g => g.place == blk.place) =
        some (K13.proverSideOfClaimCombination (I.weights Zp) (O.pile Zp G)
          (VerifiableInference.Desc.K13.whereOf Zp)) := by
  intro blk hb
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have ep : blk.place = ⟨1, none, 3, .K13⟩ :=
    Option.some.inj ((place_of_member h hb).symm.trans ps_355)
  have e := k13_half_wider hA (by rw [eZ, eG]; exact K)
  rw [eZ, eG] at e
  rw [ep, ← K13.k13Place_whereOf Zp]
  exact e

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.k7_half_head
#print axioms ProofFile.Honest.FirstFill.k13_half_head
