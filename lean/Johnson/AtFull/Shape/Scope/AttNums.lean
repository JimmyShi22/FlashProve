-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/AttNums.lean: LETTERS AND NUMBERS THAT ARE THE SAME AT TWO RECORDS THAT MEET
SameRead, AND TWO NUMBERS OF THE RETURN AT storedPublicFiles.

* testsWhere_same: the place's numbers of the tests, at every link.
* behind_same: the step of the cell behind the batching, at every link.
* k11_same: the letter k11.
* hN_of_return: at what publicOfO returns at storedPublicFiles, the head's link stands at number 24.

Limits. Equations of terms; nothing is evaluated. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.LettersSame
import Johnson.Unfolds.LedgerTables
import Johnson.HonestTrace.Run.SetUpBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (testsWhere)

variable {X X₀ : Verify.Public}

theorem testsWhere_same (S : SameRead X X₀) (i piece : Nat) :
    testsWhere X i piece = testsWhere X₀ i piece := by
  have P := S.toSamePlans
  unfold testsWhere
  dsimp only
  rw [P.p4, P.NGr, S.H, S.G,
    atA_map S (i / (if X₀.p4 = true then 2 else 1))
      (fun a => (VerifiableInference.Desc.K9.SegSort.attention, a.nLin,
      (⟨1, i, piece, a.nMsg, a.seam.nU⟩ : VerifiableInference.Desc.K9.TWhere))) fun _ => rfl]

theorem behind_same (S : SameRead X X₀) (l : Nat) :
    (TabL.behind (LW X) l).1 = (TabL.behind (LW X₀) l).1 := by
  have ew : testsWhere (LW X).XZ l 0 = testsWhere (LW X₀).XZ l 0 := testsWhere_same S l 0
  have eG : (LW X).XG.G[l / 2]? = (LW X₀).XG.G[l / 2]? := by
    show X.G[l / 2]? = X₀.G[l / 2]?
    rw [S.G]
  unfold TabL.behind
  rw [k8_same S l, ew, eG]

theorem k11_same (S : SameRead X X₀) : (LW X).k11 = (LW X₀).k11 := by
  show parAtC 76 (gOf X) = parAtC 76 (gOf X₀)
  unfold parAtC gOf
  simp only [built_same S, S.wsLay, S.frame, S.H]

/-- **At the return at storedPublicFiles the head's link is number 24.** -/
theorem hN_of_return {X₀ : Verify.Public}
    (h₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) : (if X₀.p4 = true then 2 else 1) * X₀.NGr = 24 := by
  obtain ⟨-, hG, -⟩ := HonestTraceRun.SetUp.base_facts h₀
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  have S₀ := VerifiableInference.PlanWritten.publicSteps_of_O h₀
  have h4 : X₀.p4 = true := Johnson.Unfolds.ledger_h4 VerifierAndGoals.inScope_full hR S₀.layout
  rw [if_pos h4]
  show 2 * X₀.layers.y.NGr = 24
  rw [hG]

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.testsWhere_same
#print axioms Johnson.AtFull.Shape.Scope.behind_same
#print axioms Johnson.AtFull.Shape.Scope.k11_same
#print axioms Johnson.AtFull.Shape.Scope.hN_of_return
