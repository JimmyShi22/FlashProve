-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/SwitchRowsAtScope.lean: IN THE GOALS' SCOPE, at what the proof file's plain road makes of
the three public files, at every function o in the second hash function's place, AND WHERE THE
LAYOUT FILE's GROUP LINES, AS READ, ARE THE TYPED LIST: the record of the code switch that `rowOf`
makes of the planner's own sizes and of its record of a group IS the written record of that switch,
at each of the 25; the three tests say yes at it; its target is 128; and the written list of what is
sampled goes along what the planner's record says is sent.

Why. Johnson/G/SwitchRowsAt.lean has these under eight premises on the sizes.
Johnson/Goal/Numbers/ProofLinksAtScope.lean (`eight_of_made_groups`) and ProofSizesAtPub.lean
(`eight_of_pub_groups`) have the eight in scope, under one test with code on the layout file. Here
they are joined: no premise on the sizes is left.
  `RowsWritten z sub`: what is concluded, of sizes z: six clauses at each of the 25 switches.
  `rows_of_eight`: from the eight equations on z.
  `rows_of_made_groups`: at what `ProofFile.PlainG.madeOf o` returns.
  `rows_of_pub_groups`: at the record Z that `ProofFile.pureRoad.pub o` returns: at Z.p's sizes, of which
  the seated blocks' numbers are made.
  `rows_of_made`, `rows_of_pub`: the same under the closed premise `H2K.Sizes.LayoutGroupsAre`.
Limits. ONE PREMISE IS LEFT BESIDE THE SCOPE AND THE ROAD's YES: the test on the layout file; its
closed form is proved in AtFullSide/LayoutRead/GroupsPaid.lean. That the road returns is a premise.
sub is a free letter. lo, l and kept are laid as the written record's: nothing says that they are
the planner's lists. Nothing on the running text of a block; nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.G.SwitchRowsAt
import Johnson.Goal.Numbers.ProofSizesAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open OnBytes OnBytes.Params OnBytes.Plan H2K.Sizes H2K.Member
open VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First.K2Hands (tiedB)

/-- **What is concluded of sizes z**: at each of the 25 switches, at the planner's record f of the
group into which the switch leads and the written record R of the switch: the equation; the three
tests' yes; the target; the test that ties R's list to what f says is sent. -/
def RowsWritten (z : ProofSized) (sub : Subproofs) : Prop :=
  ∀ i, i < 25 → ∀ f, (framesOf z sub)[i + 1]? = some f → ∀ R, tableFullLit[i]? = some R →
    rowOf z R.lo R.l R.kept f = R ∧ (rowOf z R.lo R.l R.kept f).ok = true ∧
      (rowOf z R.lo R.l R.kept f).writtenOK = true ∧ (rowOf z R.lo R.l R.kept f).sizedB = true ∧
      (rowOf z R.lo R.l R.kept f).set.target = 128 ∧ tiedB R.l f.sent = true

/- Lean compares these names and does not open them. -/
attribute [local irreducible] linksFull gLink szLFull codesFull2 tableFullLit groupsFull

/-- From the eight equations on the sizes. -/
theorem rows_of_eight (z : ProofSized) (sub : Subproofs) (e1 : z.set = setLit)
    (e2 : z.codes = codesFull2) (e4 : z.last.stages = szLFull) (e5 : z.link = ⟨gLink, 219⟩)
    (e6 : z.request.link = linksFull) (e7 : z.request.code = 0) (e8 : z.request.maskCode = 0)
    (e9 : z.request.answers = 1) : RowsWritten z sub := by
  intro i hi f hf R hR
  have e5' : z.link.group = gLink := by rw [e5]
  obtain ⟨p1, p2, p3, p4⟩ := row_paid z sub e6 e7 e8 e9 e5' e4 e2 e1 i hi f hf R hR
  exact ⟨row_written z sub e6 e7 e8 e9 e5' e4 e2 e1 i hi f hf R hR, p1, p2, p3, p4,
    tied_written z sub e6 e7 e8 e9 e5' e4 i hi f hf R hR⟩

/-- **IN SCOPE, AT WHAT THE PLAIN ROAD's MAKER RETURNS, UNDER THE TEST ON THE LAYOUT FILE.** -/
theorem rows_of_made_groups {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m)
    (hg0 : (Plan.layoutRead Z.lay).map (·.groups) = some groupsFull) (sub : Subproofs) :
    RowsWritten m.p.chains.made.sized.proof sub := by
  obtain ⟨e1, e2, -, e4, e5, e6, e7, e8, e9⟩ := VerifierAndGoals.Sizes.eight_of_made_groups hZ h hg0
  exact rows_of_eight _ sub e1 e2 e4 e5 e6 e7 e8 e9

/-- **IN SCOPE, AT THE RECORD THAT THE PLAIN ROAD RETURNS, UNDER THE TEST ON THE LAYOUT FILE.** -/
theorem rows_of_pub_groups {o : VerifierAndGoals.SecondHashFunctionType} {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true)
    {Z : ProofFile.Pub} (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z)
    (hg0 : (Plan.layoutRead P.lay).map (·.groups) = some groupsFull) (sub : Subproofs) :
    RowsWritten Z.p.chains.made.sized.proof sub := by
  obtain ⟨e1, e2, -, e4, e5, e6, e7, e8, e9⟩ := VerifierAndGoals.Sizes.eight_of_pub_groups hP h hg0
  exact rows_of_eight _ sub e1 e2 e4 e5 e6 e7 e8 e9

/-- The same under the closed premise on the stored layout file. -/
theorem rows_of_made {o : VerifierAndGoals.SecondHashFunctionType} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : ProofFile.PlainG.madeOf o Z.pol Z.lay Z.KL = .ok m)
    (hG : LayoutGroupsAre) (sub : Subproofs) : RowsWritten m.p.chains.made.sized.proof sub :=
  rows_of_made_groups hZ h (VerifierAndGoals.Sizes.groups_of_closed hZ hG) sub

/-- The same under the closed premise on the stored layout file. -/
theorem rows_of_pub {o : VerifierAndGoals.SecondHashFunctionType} {P : VerifierAndGoals.PublicFiles} (hP : VerifierAndGoals.InScope P = true)
    {Z : ProofFile.Pub} (h : ProofFile.pureRoad.pub o P.pol P.lay P.KL = .ok Z) (hG : LayoutGroupsAre)
    (sub : Subproofs) : RowsWritten Z.p.chains.made.sized.proof sub :=
  rows_of_pub_groups hP h (VerifierAndGoals.Sizes.groups_of_closed hP hG) sub

end Johnson.G

#print axioms Johnson.G.rows_of_eight
#print axioms Johnson.G.rows_of_made_groups
#print axioms Johnson.G.rows_of_pub_groups
#print axioms Johnson.G.rows_of_made
#print axioms Johnson.G.rows_of_pub
