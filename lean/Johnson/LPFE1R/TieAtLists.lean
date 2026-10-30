-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/LPFE1R/TieAtLists.lean: K10Heavy's FIELD hV's LAST PREMISE (P5J/K10VCfAt.lean:
k10_hV_at Zp lo seat hT): hT : ∀ i, K1.Tie (At.cs Zp) (lo.get i).1, AT THE CLOSED CONSTANT, AT THE
25 WRITTEN LISTS AND AT LINK 0's FIVE-LIST. Statements and proofs.

  tie_lists_full   BY THE KERNEL: the test tieB codesFull2 (Loose/H2K12/ClosedOfPins354.lean: kind
                   K1's four tests as one Bool) says yes at every entry of the 25 written lists
  tie_lists_no     a control: at a list whose first entry's shape has two answers the same test says
                   no
  tie_at_laid      (h : AtMg o …) (hl : l < 25) (i) : K1.Tie (At.cs Zp) ((linksFullLit.getD l
                   []).get i).1: by AtMg.codes_full
                   (P5J/CodesFullAtMg.lean) and tie_of_B (ClosedOfPins354.lean)
  tie_five_laid    the like at loFive (its entries are the six-list's)

Limits. The head AtMg is a premise: a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction;
side library AtFullSide/Top/). Of the four tests in tieB one has a
control here (answers); lengthsOk reads the codes alone; shapeOk and padFits have none here. The
full size alone. No soundness statement.

-/
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.P5J.CodesFullAtMg
import Johnson.Desc.First.Close.Law.LinkZeroFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker Johnson.G
open H2K12 (tieB tie_of_B)
open VerifiableInference.Desc.First.Close (loFive loSix)

set_option maxRecDepth 1000000 in
/-- Kind K1's four tests at every entry of the 25 written lists. -/
theorem tie_lists_full : ((List.range 25).all fun l =>
    (linksFullLit.getD l []).all fun x => tieB codesFull2 x.1) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: two answers at the first entry of link 1's list. -/
theorem tie_lists_no : (((linksFullLit.getD 1 []).take 1).map fun x =>
    ({ x.1 with answers := 2 }, x.2)).all (fun x => tieB codesFull2 x.1) = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **hT at a written list.** -/
theorem tie_at_laid (h : P5J.AtMg o Z D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (i : Fin (linksFullLit.getD l []).length) :
    K1.Tie (P5J.At.cs Zp) ((linksFullLit.getD l []).get i).1 := by
  rw [h.codes_full]
  exact tie_of_B (List.all_eq_true.1
    (List.all_eq_true.1 tie_lists_full l (List.mem_range.2 hl)) _ (List.get_mem _ i))

/-- **hT at link 0's five-list.** -/
theorem tie_five_laid (h : P5J.AtMg o Z D r Zp Np cF) (i : Fin loFive.length) :
    K1.Tie (P5J.At.cs Zp) (loFive.get i).1 := by
  rw [h.codes_full]
  have hm : loFive.get i ∈ linksFullLit.getD 0 [] :=
    (List.mem_filter.1 (List.get_mem loFive i)).1
  exact tie_of_B (List.all_eq_true.1
    (List.all_eq_true.1 tie_lists_full 0 (List.mem_range.2 (by omega))) _ hm)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tie_lists_full
#print axioms VerifiableInference.Desc.LinkJoin.tie_lists_no
#print axioms VerifiableInference.Desc.LinkJoin.tie_at_laid
#print axioms VerifiableInference.Desc.LinkJoin.tie_five_laid
