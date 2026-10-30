-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/FirstChainRuns.lean: the run on shapes over the first chain's 358 members, started from
the first shape startShA: it returns the written value border354LessPair before the proximity test
and the written value border358 at the end.
How. The 28 pieces of this library, each starting where the one before ends, joined by
Johnson/AtFull/Shape/Lines/JoinLinks.lean. No closed line stands in this file.
Main names. linkBorder: the written value before link l. links_run: the twenty-four links.
runOnShapes_toTest, runOnShapes_toEnd: the two joined facts. runOnShapes_atARecord: there is a
record, and at it the run returns. runOnShapes_yes_underHead: the conclusion of table_yes_of_runsAll
(JoinTable.lean).
Limits. These are facts on steps on shapes: guards on the structure, no field element, no test on
values; no member of the chain is shown to accept. RunsAll's run is the one over the table's second
text, shapeL (LWn X₀), which by itself is no fact on the table's own run (LettersNumerals.lean);
runOnShapes_yes_underHead goes over to the table's own steps. RunsAll speaks of every record that
publicOfO returns; runOnShapes_atARecord says that there is one. runOnShapes_yes_underHead stands
under the head AtMgA at VerifierAndGoals.storedPublicFiles and under baseOf's return: both are premises, and that they can
be met together is not shown here. It drops the last shape, it rests on further evaluations by the
kernel in the files beneath (JoinTable.lean's head lists some), and it pays one premise among
several of RuleAtTable.lean's laws. border353LessPair and border354LessPair are compared in all
components by the lines that end at them.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinLinks
import AtFullSide.Layout.Size
import ShapeLines.Front.FrontMember
import ShapeLines.Layers.Link0Runs
import ShapeLines.Attention.Link1Runs
import ShapeLines.Layers.Link2Runs
import ShapeLines.Attention.Link3Runs
import ShapeLines.Layers.Link4Runs
import ShapeLines.Attention.Link5Runs
import ShapeLines.Layers.Link6Runs
import ShapeLines.Attention.Link7Runs
import ShapeLines.Layers.Link8Runs
import ShapeLines.Attention.Link9Runs
import ShapeLines.Layers.Link10Runs
import ShapeLines.Attention.Link11Runs
import ShapeLines.Layers.Link12Runs
import ShapeLines.Attention.Link13Runs
import ShapeLines.Layers.Link14Runs
import ShapeLines.Attention.Link15Runs
import ShapeLines.Layers.Link16Runs
import ShapeLines.Attention.Link17Runs
import ShapeLines.Layers.Link18Runs
import ShapeLines.Attention.Link19Runs
import ShapeLines.Layers.Link20Runs
import ShapeLines.Attention.Link21Runs
import ShapeLines.Layers.Link22Runs
import ShapeLines.Attention.Link23Runs
import ShapeLines.Head.HeadLinkRuns
import ShapeLines.Back.FinishMember
import ShapeLines.Back.BackFromTest

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape

/-- The written value before link l, for l = 0 to 23; at 24 the one before the head's link; beyond
24 it answers border1. -/
def linkBorder (l : Nat) : ShA :=
  [border1, border15, border29, border43, border57, border71, border85, border99, border113,
    border127, border141, border155, border169, border183, border197, border211, border225,
    border239, border253, border267, border281, border295, border309, border323, border337].getD l
    border1

/-- Each of the twenty-four links runs from the written value before it to the next. -/
theorem links_run :
    ∀ l, l < 24 → RunsAll (14 * l + 1) 14 (linkBorder l) (linkBorder (l + 1)) :=
  fun l hl => match l, hl with
    | 0, _ => layersLink0_runs
    | 1, _ => attentionLink1_runs
    | 2, _ => layersLink2_runs
    | 3, _ => attentionLink3_runs
    | 4, _ => layersLink4_runs
    | 5, _ => attentionLink5_runs
    | 6, _ => layersLink6_runs
    | 7, _ => attentionLink7_runs
    | 8, _ => layersLink8_runs
    | 9, _ => attentionLink9_runs
    | 10, _ => layersLink10_runs
    | 11, _ => attentionLink11_runs
    | 12, _ => layersLink12_runs
    | 13, _ => attentionLink13_runs
    | 14, _ => layersLink14_runs
    | 15, _ => attentionLink15_runs
    | 16, _ => layersLink16_runs
    | 17, _ => attentionLink17_runs
    | 18, _ => layersLink18_runs
    | 19, _ => attentionLink19_runs
    | 20, _ => layersLink20_runs
    | 21, _ => attentionLink21_runs
    | 22, _ => layersLink22_runs
    | 23, _ => attentionLink23_runs
    | n + 24, h => absurd h (by omega)

/-- At every record that publicOfO returns at the stored full-size files: started from startShA, the
steps on shapes of members 0 to 353 return border354LessPair. -/
theorem runOnShapes_toTest : RunsAll 0 354 startShA border354LessPair :=
  run_to_test linkBorder border353LessPair border354LessPair frontMember_runs links_run
    headLink_runs finishMember_runs

/-- At every record that publicOfO returns at the stored full-size files: started from startShA, the
steps on shapes of all 358 members return border358. -/
theorem runOnShapes_toEnd : RunsAll 0 358 startShA border358 :=
  run_whole linkBorder border353LessPair border354LessPair border358 frontMember_runs links_run
    headLink_runs finishMember_runs backFromTest_runs

/-- There is a record that publicOfO returns at the stored full-size files, and at it the run on
shapes over all 358 members, started from startShA, returns border358. -/
theorem runOnShapes_atARecord :
    ∃ X₀ : OnBytes.Model.Verify.Public,
      VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
        (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      (shapeL (LWn X₀)).runFrom 0 358 startShA = .ok border358 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size runOnShapes_toEnd

open OnBytes.Maker (WholeD) in
open P5J (AtMgA) in
/-- Under the head at the stored full-size files and where baseOf returns: started from startShA,
the run on shapes over the table's own steps returns at all 358 members. This is premise hyes of
RuleAtTable.lean's laws on the first chain, at a₀ := startShA. It is no accept. -/
theorem runOnShapes_yes_underHead
    {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true :=
  table_yes_of_links Johnson.Unfolds.Layout.lay_size h hB linkBorder border353LessPair
    border354LessPair border358 frontMember_runs links_run headLink_runs finishMember_runs
    backFromTest_runs

end ShapeLines

#print axioms ShapeLines.links_run
#print axioms ShapeLines.runOnShapes_toTest
#print axioms ShapeLines.runOnShapes_toEnd
#print axioms ShapeLines.runOnShapes_atARecord
#print axioms ShapeLines.runOnShapes_yes_underHead
