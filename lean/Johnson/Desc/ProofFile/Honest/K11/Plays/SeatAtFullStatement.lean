-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/SeatAtFullStatement.lean: THE PREMISE "member" OF
`HeadMergeGoodSeated` (SLotStatement.lean of this folder) AT THE FIRST CHAIN's OWN LIST OF MEMBERS
AT THE FULL SIZE; AND THE FRAME's `Good` THERE, AT A' := B' := False (plays AND acc HOLD FROM False:
NOTHING IS SHOWN BY THEM): STATEMENTS ALONE: three, each a definition of a proposition. NOTHING IS
PROVED IN THIS FILE, and none of the three is one of the library's goals: they are lemmas'
statements. WHAT FOLLOWS FROM `Good` IS NOT SAID HERE.

Under the library's one hypothesis at the full size (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean) member
number 346 of the first chain's flat list is the kind's block as it stands alone at a seat, at the
numbers at which the lot lays it (`HeadMergeAtFull`,
Johnson/Desc/K11/Exchange/AtFullStatement.lean). The frame takes a side's sub-protocol off a list BY
ITS PLACE: the first member at that place (`Side.seated`, Honest/Side.lean). Here: that the two
meet.

  `HeadMergePlaceIs`       the place in which the honest row is written (`headMergePlace`,
                           Honest/K11/Part.lean) is the kind's block's own field place
  `HeadMergeMemberAtFull`  under the hypothesis, and where no two members of the first chain's flat
                           list stand at one place: the first member at the row's place is the
                           kind's block at its seat at that place: "member", at bs := the flat list
  `HeadMergeGoodAtFull`    under these two, "seated" and "unspent": `Good` at the side that
                           `Side.seated` takes off the flat list, at A' := B' := False and the row's
                           own On and bud

Limits. The hypothesis is a premise: it is shown at no file here; it stands at the earlier hash.
That no two members stand at one place is a premise on the list. "unspent" is shown at no book.
plays and acc hold from False: nothing is shown by them. Of exact: all that GoodAllStatement.lean of
this folder says in its Limits holds here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.SLotStatement
import Johnson.Desc.K11.Exchange.AtFullStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind)

/-- The statement on the two places. Not proved here; a lemma's statement, none of the library's
goals. -/
def HeadMergePlaceIs : Prop := ∀ P : HeadMergeP, headMergePlace P = (headClaimMergeKind P).place

/-- The statement on the first member at the row's place. The letters: the hypothesis's own. Not
proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeMemberAtFull : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x → (cF.blocksInOrder.map (·.place)).Nodup →
    ∃ (Bs : ProofFile.PureBase) (name : String),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      (cF.blocksInOrder.find? fun b => b.place == headMergePlace (_root_.K11.parOf Zp Bs.G₀)) =
        some (IM.seatedAs ProofFile.sameReply (headClaimMergeKind (_root_.K11.parOf Zp Bs.G₀)) name
          (headMergePlace (_root_.K11.parOf Zp Bs.G₀)))

/-- The statement on `Good`. Bs: what the maker's base returns at the public part. pre is tied to no
description. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeGoodAtFull : Prop :=
  ∀ (W₀ Rc Xi Tr X : Type) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF)
    (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (x : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase) (fs₀ : List (Fall S))
    (σ₀ : Side S ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (claims : Xi → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x → (cF.blocksInOrder.map (·.place)).Nodup →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    Side.seated cF.blocksInOrder
      (headMergeBare (Rc := Rc) (Tr := Tr) (X := X) (_root_.K11.parOf Zp Bs.G₀) claims
        weights).place
      (headMergeBare (_root_.K11.parOf Zp Bs.G₀) claims weights).row fs₀ = some σ₀ →
    (∀ j q, Bk.spentBy ⟨headMergePlace (_root_.K11.parOf Zp Bs.G₀), j⟩ q = []) →
    Good pre φ σ₀ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (headMergeBare (Rc := Rc) (Tr := Tr) (X := X) (_root_.K11.parOf Zp Bs.G₀) claims weights).On
      (headMergeBare (Rc := Rc) (Tr := Tr) (X := X) (_root_.K11.parOf Zp Bs.G₀) claims weights).bud

end ProofFile.Honest.K11
