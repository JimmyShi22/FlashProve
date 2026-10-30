-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/KeyRec/Once.lean: the sizes of the test on the table of a key of full size are what
Params.linSized returns: the six sizings of the files beside and the three tests' stages, joined.

Main names.
  keyTurns, keyFinish, keyLin_sized.

Limits. keyFinish is one evaluation in Lean's kernel, a small one (about a second). Closed
statements at the typed values alone. One direction: from a linSized that returns; its refusals are
not evaluated here. That a key's sizing calls linSized at these arguments is not said here
(Johnson/Goal/PlanValues/KeySizesAtPlan.lean). Nothing on soundness. For proofs only; the program
does not import this file.

-/
import OnBytes.Params.KeyRec.Once1x
import OnBytes.Params.KeyRec.Once1y
import OnBytes.Params.KeyRec.Once1z
import OnBytes.Params.KeyRec.Once2x
import OnBytes.Params.KeyRec.Once2y
import OnBytes.Params.KeyRec.Once2z
import OnBytes.Params.KeyRec.Folded
import OnBytes.Params.KeyRec.Omega
import OnBytes.Params.KeyRec.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace OnBytes.Params

/-- **The iteration over the three groups**: two turns. -/
theorem keyTurns :
    linTurns recordSet keyLin (linGroupsOf recordSet keyLin recordTable) 33 {} {} {} =
      some (keyX1, keyY1, keyZ1) := by
  rw [keyGroups_eq]
  exact (linTurns_step (fuel := 32) rfl keyTurn1_x keyTurn1_y keyTurn1_z).trans
    ((if_neg (by decide)).trans
      ((linTurns_step (fuel := 31) rfl keyTurn2_x keyTurn2_y keyTurn2_z).trans
        (if_pos (by decide))))

/-- What linSized's text makes of the solved groups and stages. -/
theorem keyFinish : linFinish recordSet keyLin recordTable {} keyX1 keyY1 keyZ1 keyUStages
    keyOStages keyWStages = some (keyOnceRec, keyCodes1) := by
  decide +kernel

/-- **Whatever linSized returns at these lines, this table and no codes is the typed value.** -/
theorem keyLin_sized {x : LinSized} {c : Codes}
    (h : linSized recordSet keyLin recordTable {} = some (x, c)) :
    x = keyOnceRec ∧ c = keyCodes1 := by
  obtain ⟨X, Y, Z, stU, stO, stW, hT, hU, hO, hW, hF⟩ := linSized_named h
  have e0 := Option.some.inj (hT.symm.trans keyTurns)
  obtain ⟨rfl, e1⟩ := Prod.mk.inj e0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  rw [if_pos (show linSplit keyLin = true by decide)] at hO
  have hU' : solveStages recordSet .once keyU1 97 recordLines.onceFolded.stages
      = some stU := hU
  have hO' : solveStages recordSet .once keyO1 49 recordLines.onceOmega.stages
      = some stO := hO
  have hW' : solveStages recordSet .once keyW1 49 recordLines.onceOwn.stages
      = some stW := hW
  obtain rfl : stU = keyUStages := Option.some.inj (hU'.symm.trans keyU_stages)
  obtain rfl : stO = keyOStages := Option.some.inj (hO'.symm.trans keyO_stages)
  obtain rfl : stW = keyWStages := Option.some.inj (hW'.symm.trans keyW_stages)
  have e2 := Option.some.inj (hF.symm.trans keyFinish)
  exact ⟨(Prod.mk.inj e2).1, (Prod.mk.inj e2).2⟩

end OnBytes.Params

#print axioms OnBytes.Params.keyTurns
#print axioms OnBytes.Params.keyFinish
#print axioms OnBytes.Params.keyLin_sized
