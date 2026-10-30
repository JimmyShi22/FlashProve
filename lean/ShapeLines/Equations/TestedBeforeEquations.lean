-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Equations/TestedBeforeEquations.lean: before each of the twenty-five members "the one
equation" of the first chain (members 14 l + 11 for l below 24, and member 349), the shape that the
run on shapes returns from startShA passes equationTest.
How. This folder's twenty-five facts, each from the written value before its link, with the front
and the links before it (ShapeLines/FirstChainRuns.lean), by RunsToTested.fromStart
(Johnson/AtFull/Shape/Lines/JoinTested.lean). No closed line stands in this file.
What it is for. The table's test at the member "the one equation" is oneV
(Johnson/AtFull/Shape/ValsBool.lean). By its own file's head, ProofFile.Honest.K9.oneShape
(Johnson/Desc/ProofFile/Honest/K9/EqShape.lean) is all that oneV still asks of the public data, as
one Bool on the chain's shape. It reads no field element, and a pass does not by itself give oneV.
The fact has the form RunsToTested (Johnson/AtFull/Shape/Lines/JoinTested.lean): the run returns
some shape, and the test accepts it. So no value is written for the shape before that member, which
lies inside a link, where components of the shape are long (ShapeLines/README.md). The fact's user
is the premise eqSizesYes (Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean): unfolded, that premise
is this fact over the table's own steps (RunsToTested.atTable).
Limits. RunsToTested speaks of every record that publicOfO returns at the stored full-size files and
does not say that there is one, nor which shape the run returns. Its run is the one over
shapeL (LWn X₀), the text of the table over a record of letters
(Johnson/AtFull/Shape/TabLetters.lean); RunsToTested.atTable and RunsToTested.atState take a fact
from startShA to the table's own steps and to a state, under the premise AtMgA and further premises.
What a pass means is said in the head of Johnson/Desc/ProofFile/Honest/K9/EqShape.lean. That members
14 l + 11 and 349 are of the kind "the one equation" is Johnson/AtFull/Shape/Table.lean's numbering;
no law of this library ties a kind to a number; cell_at
(Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean) does.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinTested
import ShapeLines.FirstChainRuns
import ShapeLines.Equations.HeadLinkBeforeEquation
import ShapeLines.Equations.LayersLink0BeforeEquation
import ShapeLines.Equations.AttentionLink1BeforeEquation
import ShapeLines.Equations.LayersLink2BeforeEquation
import ShapeLines.Equations.AttentionLink3BeforeEquation
import ShapeLines.Equations.LayersLink4BeforeEquation
import ShapeLines.Equations.AttentionLink5BeforeEquation
import ShapeLines.Equations.LayersLink6BeforeEquation
import ShapeLines.Equations.AttentionLink7BeforeEquation
import ShapeLines.Equations.LayersLink8BeforeEquation
import ShapeLines.Equations.AttentionLink9BeforeEquation
import ShapeLines.Equations.LayersLink10BeforeEquation
import ShapeLines.Equations.AttentionLink11BeforeEquation
import ShapeLines.Equations.LayersLink12BeforeEquation
import ShapeLines.Equations.AttentionLink13BeforeEquation
import ShapeLines.Equations.LayersLink14BeforeEquation
import ShapeLines.Equations.AttentionLink15BeforeEquation
import ShapeLines.Equations.LayersLink16BeforeEquation
import ShapeLines.Equations.AttentionLink17BeforeEquation
import ShapeLines.Equations.LayersLink18BeforeEquation
import ShapeLines.Equations.AttentionLink19BeforeEquation
import ShapeLines.Equations.LayersLink20BeforeEquation
import ShapeLines.Equations.AttentionLink21BeforeEquation
import ShapeLines.Equations.LayersLink22BeforeEquation
import ShapeLines.Equations.AttentionLink23BeforeEquation

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

/-- At every record that publicOfO returns at the stored full-size files: in each of the twenty-four
links, from the written value before the link, its first ten members return a shape that
equationTest accepts. -/
theorem links_testedBeforeEquation :
    ∀ l, l < 24 → RunsToTested (14 * l + 1) 10 (fun _ => linkBorder l) equationTest :=
  fun l hl => match l, hl with
    | 0, _ => layersLink0_testedBeforeEquation
    | 1, _ => attentionLink1_testedBeforeEquation
    | 2, _ => layersLink2_testedBeforeEquation
    | 3, _ => attentionLink3_testedBeforeEquation
    | 4, _ => layersLink4_testedBeforeEquation
    | 5, _ => attentionLink5_testedBeforeEquation
    | 6, _ => layersLink6_testedBeforeEquation
    | 7, _ => attentionLink7_testedBeforeEquation
    | 8, _ => layersLink8_testedBeforeEquation
    | 9, _ => attentionLink9_testedBeforeEquation
    | 10, _ => layersLink10_testedBeforeEquation
    | 11, _ => attentionLink11_testedBeforeEquation
    | 12, _ => layersLink12_testedBeforeEquation
    | 13, _ => attentionLink13_testedBeforeEquation
    | 14, _ => layersLink14_testedBeforeEquation
    | 15, _ => attentionLink15_testedBeforeEquation
    | 16, _ => layersLink16_testedBeforeEquation
    | 17, _ => attentionLink17_testedBeforeEquation
    | 18, _ => layersLink18_testedBeforeEquation
    | 19, _ => attentionLink19_testedBeforeEquation
    | 20, _ => layersLink20_testedBeforeEquation
    | 21, _ => attentionLink21_testedBeforeEquation
    | 22, _ => layersLink22_testedBeforeEquation
    | 23, _ => attentionLink23_testedBeforeEquation
    | n + 24, h => absurd h (by omega)

/-- At every record that publicOfO returns at the stored full-size files: from startShA, the first
14 l + 11 members of the run on shapes return a shape that equationTest accepts: the shape before
the one equation of link l. -/
theorem firstChain_testedBeforeEquation (l : Nat) (hl : l < 24) :
    RunsToTested 0 (14 * l + 11) (fun _ => startShA) equationTest :=
  RunsToTested.fromStart linkBorder l frontMember_runs
    (fun k hk => links_run k (Nat.lt_trans hk hl)) (links_testedBeforeEquation l hl)

/-- At every record that publicOfO returns at the stored full-size files: from startShA, the first
349 members of the run on shapes return a shape that equationTest accepts: the shape before the one
equation of the head's link. -/
theorem firstChain_testedBeforeHeadEquation :
    RunsToTested 0 349 (fun _ => startShA) equationTest :=
  RunsToTested.fromStart linkBorder 24 frontMember_runs links_run (k := 12)
    headLink_testedBeforeEquation

end ShapeLines

#print axioms ShapeLines.links_testedBeforeEquation
#print axioms ShapeLines.firstChain_testedBeforeEquation
#print axioms ShapeLines.firstChain_testedBeforeHeadEquation
