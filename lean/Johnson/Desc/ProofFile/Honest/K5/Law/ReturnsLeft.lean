-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsLeft.lean: CONDITIONAL: WHAT IS LEFT OF "THE MAKER
onlineProverFromPublicFiles RETURNS AT THE HEAD's THREE FILES AND THE FILLING widerFillAt", AS ONE THEOREM's OWN BINDERS,
with the lines of K4, K5 and K6 called.

Why. Many laws on the honest prover take "onlineProverFromPublicFiles returns" as a premise. ReturnsAtWider.lean says in
which named parts that premise falls (`MakerHas`, `WiderDebts`); ReturnsHead.lean pays three of the
maker's four parts under the head. Here the parts that are proved are called, so that what is left
can be read off one statement.

Main name:
  `atPure_returns_left`: under the head and the library's test on the head's public files, at every
    I, o', S and O: the maker returns, at the head's public part and description. Its binders: book
    (the book's maker returns); k1, k2, k7, k11, k3, k8, k13 (no half of that kind's list strays in
    the first chain); k14 (the same of the shared chain); range.

Called: `K4.k4HLot_noStray_desc` (Johnson/Desc/ProofFile/Honest/K4/Law/LotNoStrayOpen.lean),
`K6.headLot_noStray_desc` (Johnson/Desc/ProofFile/Honest/K6/Law/HalfNoStray.lean), whose premise on
the last link comes of the library's `IM.ground_gets` and `IM.subs_head`, and K5's own line inside
`widerOwn_returns`.

Limits. An implication: none of the binders is proved here; ReturnsLeftFour.lean calls six of them.
k13 and k14 are typed as the fields of `WiderDebts`: premises here: not proved in this file or
beneath it. They are met above it: k13 in ReturnsLeftThree.lean (by `K13.k13Lot_no_strays_light`),
k14 in ReturnsLeftTwo.lean (by `K14.wider_k14_light`). The head is a hypothesis, and so is the
library's test. The head and the library's test have a member together at the library's written copy
of the full-size public files (`AtFullSide.Top.headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the package's files by no theorem. At the
library's full size and the function `OnBytes.secondHashFunction` alone. Through its imports the file stands
above the files under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsAtWider
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsHead
import Johnson.Desc.ProofFile.Honest.K4.Law.LotNoStrayOpen
import Johnson.Desc.ProofFile.Honest.K6.Law.HalfNoStray

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}

/-- **WHAT IS LEFT.** Conditional: h: the head; hl: the library's test on the head's public files;
book: the book's maker returns; k1, k2, k7, k11, k3, k8: no half of these six kinds' lists strays in
the first chain; k13, k14: the same of K13's list, and of the shared chain's, each typed as the
field of `WiderDebts`; range: the named member of the index's range is in range. K4's, K5's and K6's
lines are called. -/
theorem atPure_returns_left (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B)
    (k1 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((K1.dataSideNo S (fun w : Local W₀ IndexCommitterCoins Inst Cells =>
          ⟨w.x, ⟨w.trace, I.weights Zp w.w₀, w.rc⟩⟩) o' : WLot W₀ Unit).halves Zp G) = [])
    (k2 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((K2.switchLot (widerRows S Zp G) fun w : Local W₀ IndexCommitterCoins Inst Cells =>
          ⟨w.trace, I.weights Zp w.w₀, w.rc⟩ : WLot W₀ Unit).halves Zp G) = [])
    (k7 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((replyLot : WLot W₀ Unit).halves Zp G) = [])
    (k11 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((K11.headMergeLot O.claims (I.weights Zp) : WLot W₀ Unit).halves Zp G) = [])
    (k13 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((K13.k13Lot (I.weights Zp) O.pile : WLot W₀ Unit).halves Zp G) = [])
    (k3 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((K3.theLotInst id (I.weights Zp) : WLot W₀ Unit).halves Zp G) = [])
    (k8 : ∀ G, blankBy pureRoad.links Zp = some G →
      strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
        ((K8.smallLot id fun _ G _ l => K3.matsOwn G.W l : WLot W₀ Unit).halves Zp G) = [])
    (k14 : strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
      ((nowSharedBy (I.weights Zp) Zp).toOption.getD []) = [])
    (range : I.inRange I.dummy = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := by
  obtain ⟨G, B, m⟩ := made_live h hl book
  have hlast : (ProofFile.subsOf Zp)[G.built.size - 1]? = some .head := by
    rw [(IM.ground_gets h.scope h.reads h.laid.pub m.ground).1]
    exact IM.subs_head h.scope h.reads h.laid.pub m.ground
  obtain ⟨A, hA, eZ, _, eF, _⟩ := widerOwn_returns (own₀ := ()) (o' := o') (O := O) m
    (L := LongLots.plain (X := Unit) o' S O) (I := I) (S := S)
    { k1 := k1 G m.ground, k2 := k2 G m.ground, k7 := k7 G m.ground, k11 := k11 G m.ground
      k13 := k13 G m.ground, k3 := k3 G m.ground
      k4 := K4.k4HLot_noStray_desc m.pub m.ground m.desc id (I.weights Zp) fun _ _ => K4.k4LookAt
      k6 := K6.headLot_noStray_desc m.pub m.ground m.desc hlast K6.headFitsB
        (K6.headWit' id (I.weights Zp))
      k8 := k8 G m.ground, k14 := k14, range := range }
  exact ⟨A, hA, eZ, eF⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.atPure_returns_left
