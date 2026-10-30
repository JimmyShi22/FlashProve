-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Later/Open.lean: five of the facts that the return of the proof file's maker asks of
the proof file's description (the premises hC, hD, b₂, b₃, hFo of `proofLaid_of_desc`,
Johnson/AtFull/Top/ProofLaidOfDesc.lean), from the
ten facts on the two later chains (`LaterPaid`, Johnson/AtFull/Later/Paid.lean) and two facts on
the first chain. A joining: nothing is evaluated here.

  `open_of_later`: at the description FW … A B c made of the two seats and a first chain c:
    the three cuts are the written ones · the declared rounds are the written ones · each
    sub-protocol of the two later chains passes its test on the plan · the description's own test
    on the plan passes. Premises beside `LaterPaid`: e1 (the planner's four free parts are the
    written ones), and of the first chain c₁ (its cut) and d₁ (its declared rounds).

By: the description lays `first := c`, `shared := A.chain.retype`, `second := B.chain.retype`
(Johnson/Desc/ProofFile/Frames1.lean), so each field is the like-named fact by unfolding. The test
on the plan is four tests: the two seats', and two on what the planner made, which
`hF_of_free` (Johnson/AtFull/ProofPlan/EveryWritten.lean) pays from e1.

Limits. c₁ AND d₁ ARE PREMISES: the first chain is not spoken of here. Nothing on soundness or on
hiding.

-/
import Johnson.AtFull.Later.Paid
import Johnson.AtFull.ProofPlan.EveryWritten
import Johnson.AtFull.ProofRows.Join14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Later
open VerifiableInference.PlanWritten (cutIs cutFirstFull)
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open Johnson.AtFull.Pub (DW)
open Johnson.G.OfPlan (Made)
open _root_.AtFull.Top (ZqM FW)

/-- **The description's five, from the two later chains' ten and the first chain's two.** -/
theorem open_of_later {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray} {m : Made} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (L : LaterPaid (ZqM pol KL m) A B)
    (e1 : Johnson.G.MadeFree.freeOf m.p.chains.made = writtenMade) (c : Chain S ProofFile.Cl)
    (c₁ : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (d₁ : c.blocksInOrder.flatMap (·.rounds) = DW.1) :
    cutIs (FW o pol KL m A B c) = true ∧ (FW o pol KL m A B c).roundsDeclaredByBlocks = DW ∧
      (∀ b ∈ (FW o pol KL m A B c).shared.blocksInOrder, b.planOk = true) ∧
      (∀ b ∈ (FW o pol KL m A B c).second.blocksInOrder, b.planOk = true) ∧
      (FW o pol KL m A B c).fileOk = true :=
  ⟨Johnson.AtFull.ProofRows.Fourteen.row10 (F := FW o pol KL m A B c) (Zp := ZqM pol KL m) c₁ L.c₂
      L.c₃,
    Prod.ext d₁ (Prod.ext L.d₂ L.d₃), L.b₂, L.b₃,
    Johnson.AtFull.ProofPlan.hF_of_free _ _ _ _ _ _ _ _ L.fA L.fB e1⟩

end Johnson.AtFull.Later

#print axioms Johnson.AtFull.Later.open_of_later
