-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TestNumbersAtHead.lean: UNDER THE HYPOTHESIS `P5J.AtMg` THE NUMBERS OF THE
FIRST CHAIN's LAST PROXIMITY TEST, `H2U.p12OfMade Zp.made` (Johnson/Desc/K12/AtPlan.lean), ARE THE
WRITTEN RECORD `H2K.Member.piLFull` (Johnson/Desc/K12/Law/PlacesFull.lean): A CLOSED TERM. With it
the like for the same kind's three sub-protocols on the two later chains, at the pieces 9, 10 and 2.
The proofs only combine laws of the library; nothing is evaluated here.

Words. `P5J.AtMg` (Johnson/P5J/AtMg.lean) is the library's hypothesis at the full size; the library
calls it "the head". Below: the hypothesis.

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's blocksInOrder list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. This equation is meant for its step at number 354, the last proximity test.

How. The library has the four equations from five premises (`members_written_front`,
Johnson/Loose/H2K12/K12MemberFront.lean): that the public part Zp is what `ProofFile.pureRoad.pub`
(Johnson/Desc/ProofFile/OnlineDescriptionPublicPart.lean) returns at the three public files, and four equations on
fields: the setting, the proof file's sizes, the planner's three lists, what is sent. In the goals'
scope, where the entry test on what the planner configured accepts, these four are theorems
(`made_in_scope`, `proof_plans_in_scope`, `sends_in_scope`, Johnson/Goal/Numbers/MadeInScope.lean).
The hypothesis gives the first premise (its field laid.pub), the scope, and that entry test's accept
(`AtMg.pins`, Johnson/P5T/FenceAtMg.lean; `pinnedAt_of_row`,
Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean).

Main names.
* `p12_four_at_head`: H2U.p12OfMade Zp.made = piLFull; and p12FoldedOfMade at piece 9,
  p12OmegaOfMade at piece 10, p12OwnOfMade at piece 2 are piUFull, piOFull, piWFull, each with its
  field place replaced by ⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩, ⟨3, none, 2, .K12⟩. These three
  functions take the piece as an argument: the statement speaks of these three pieces alone.
* **`p12_at_head`**: the first of the four.

Limits. UNDER THE HYPOTHESIS. That the hypothesis can be met is shown only for `P5J.AtMgA`, which
extends AtMg, at the hash OnBytes.secondHashFunction and at two named sets of public files (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean; `headMember_zGap`, AtFullSide/Top/HeadMemberAtGap.lean); by
the first file's own words the example's weights are synthetic. NO ENTRY TEST COMPARES ANYTHING WITH
piLFull. The entry test named above is four tests (`madePinned`, MadeTestLaws.lean). With written
values they compare: the planner's sizes of a proof file and the FIRST of its three lists of rounds,
no other list (`madeIs`); six fields of the first chain's parameters (`firstIs`; both in
MadeTest.lean, in the same folder); the proof file's three lists of what is sent (`proofSendsIs`,
SendsTest.lean there); the shape part of what `verify-on-bytes`'s reader makes of the public files
(`xShapeIs`, XShapeTest.lean there). The planner's two other lists of rounds are the written ones by
a theorem, in the goals' scope and where that test accepts (`proof_plans_in_scope`). piLFull is tied
to these written values by a theorem (`members_written`, Johnson/Loose/H2K12/K12MemberWritten.lean);
by that file's opening comment the written values rest on prints of the library's own planner and
evaluator. Only the full-size parameters are covered. Nothing on soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.K12MemberFront
import Johnson.Goal.Numbers.MadeInScope
import Johnson.P5T.FenceAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.PlanWritten (pinnedAt_of_row)
open VerifiableInference.PlanWritten.Joined (made_in_scope proof_plans_in_scope sends_in_scope
  writtenSized)
open Johnson.G.MadeFree (Free)
open OnBytes.Maker (WholeD)
open P5J (AtMg)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **Under the hypothesis the kind K12's four records off the plan are written records**: the first
as it stands; the other three with the field place replaced, at the pieces 9, 10 and 2. -/
theorem p12_four_at_head (h : AtMg o Z D r Zp Np cF) :
    H2U.p12OfMade Zp.made = H2K.Member.piLFull ∧
      H2U.p12FoldedOfMade Zp.made 9 =
        ({ H2K.Member.piUFull with place := ⟨2, none, 9, .K12⟩ } : P12) ∧
      H2U.p12OmegaOfMade Zp.made 10 =
        ({ H2K.Member.piOFull with place := ⟨2, none, 10, .K12⟩ } : P12) ∧
      H2U.p12OwnOfMade Zp.made 2 =
        ({ H2K.Member.piWFull with place := ⟨3, none, 2, .K12⟩ } : P12) := by
  have hZ : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp := h.laid.pub
  obtain ⟨hm, -⟩ := h.pins
  have hy := pinnedAt_of_row (Z := Zp) (by rw [hm, Bool.or_true])
  have hsz : Zp.p.chains.made.sized = writtenSized :=
    congrArg Free.sized (made_in_scope h.scope hZ hy)
  exact H2K12.members_written_front hZ (by rw [hsz]; rfl) (by rw [hsz]; rfl)
    (proof_plans_in_scope h.scope hZ hy) (sends_in_scope h.scope hZ hy)

/-- **UNDER THE HYPOTHESIS THE NUMBERS OF THE FIRST CHAIN's LAST PROXIMITY TEST ARE THE WRITTEN
RECORD piLFull.** -/
theorem p12_at_head (h : AtMg o Z D r Zp Np cF) :
    H2U.p12OfMade Zp.made = H2K.Member.piLFull := (p12_four_at_head h).1

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.p12_four_at_head
#print axioms Johnson.AtFull.Shape.p12_at_head
