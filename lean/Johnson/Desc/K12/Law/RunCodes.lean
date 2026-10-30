-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.OutK2
/-
Johnson/Desc/K12/Law/RunCodes.lean: TWO THINGS THAT A YES OF THE PROXIMITY TEST's BLOCK LAYS, WITH NO PREMISE ON THE PLACE BUT THE BLOCK's OWN TEST ON THE PLAN: the test of the group under test has begun · the codes stand. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. OF proximityTestKind guardedProximityTestParts p.
  k12_run_codes   planOk · a yes of the decision, from t0 to tE ⇒ (∃ G, tE.st.groups[t0.g]? = some G ∧ G.inRun = true) ∧ tE.st.codes = t0.st.codes
HOW: OutK2.begunG (k12_out2, Johnson/Desc/K12/Law/OutK2.lean) and OutK.codes (k12_out, Johnson/Desc/K12/Law/OutK.lean), whose two premises on the place fall to the block's test on the plan: OVER THE JOINED PARTS that test asks both (early_of_planOk · answers_of_planOk, Johnson/Desc/K12/Law/Top.lean).
(Where this and lean/THEOREM.md differ,
the page holds.)
WHAT FOR: two of the four debts that the last chain's book-keeping names at the step over the request's own test («the own group's test has begun» · «the codes stay»). The third («the named values stay») is the seat's own text: it lays back the statement, the book and the roots alone. THE FOURTH («the statement behind is tidy») IS NOT HERE.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK

theorem k12_run_codes (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    (∃ G, tE.st.groups[t0.g]? = some G ∧ G.inRun = true) ∧ tE.st.codes = t0.st.codes := by
  have he := early_of_planOk p hp
  have ha := answers_of_planOk p hp
  obtain ⟨G, h2⟩ := k12_out2 p he ha t0 tE rs gs h
  exact ⟨⟨_, h2.begunG, rfl⟩, (k12_out p he ha t0 tE rs gs h).codes⟩

end H2K.Out

#print axioms H2K.Out.k12_run_codes
