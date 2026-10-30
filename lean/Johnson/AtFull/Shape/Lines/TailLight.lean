-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/TailLight.lean: the light cells of the run on shapes (`cellsH2`,
Johnson/AtFull/Shape/LookLight.lean) with light cells at the head's link too, and the tie: they are
the light cells of Johnson/AtFull/Shape/TabLight.lean, at every hint, letters and number, with no
premise. So the run over them is `runH` of Johnson/AtFull/Shape/JoinPieces.lean.

The two cells. At member 350, the head's closing: `closeGFH` at the hint of link 24, as
`cellsH` has at the links 0 to 23. At member 340, the head's lookup on the calls: `callsGL`, as
`cellsH2` has at the links 0 to 23. Where a cell's letters are lacking the cell is that of
`cellsH2`.

Main names.
  `lightTailCells`, `lightTailCells_eq`   the cells and the tie.
  `runOverLightTail`, `runOverLightTail_eq`, `runOverLightTail_fun`   the run of k members from m on
      over these cells at `LWn X`, and that it is `runH`.

Limits. Equations of terms: that a cell is light is said by no theorem. Nothing says that a step
returns, and nothing is evaluated here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LookLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open ProofFile.Honest.K10.YesFree (closeGFH)

/-- **The light cells with the head's closing and the head's lookup on the calls.** -/
def lightTailCells (hint : Nat → List (Nat × Nat)) (L : TabLetters) (n : Nat) : Cell :=
  if n = 350 then
    match L.close 24 with
    | some Q => (optE (closeGFH.1 (hint 24) Q), (TabL.cells L 350).2)
    | none => cellsH2 hint L n
  else if n = 340 then
    match L.look 24 false with
    | some s => (liftQ (callsGL s.1 s.2), noVals)
    | none => cellsH2 hint L n
  else cellsH2 hint L n

/-- **The tie**: at every hint, letters and number. No premise. -/
theorem lightTailCells_eq (hint : Nat → List (Nat × Nat)) (L : TabLetters) (n : Nat) :
    lightTailCells hint L n = cellsH hint L n := by
  unfold lightTailCells
  by_cases atClose : n = 350
  · subst atClose
    rw [if_pos rfl]
    have table350 : cellsH hint L 350 = TabL.close L 24 := by
      unfold cellsH
      rw [if_pos (Or.inr (by omega))]
      exact table_head _ _ _ _ 13 (by omega)
    cases closing : L.close 24 with
    | none => exact cellsH2_eq hint L 350
    | some Q =>
      have same : closeGFH.1 (hint 24) Q = ProofFile.Honest.K10.YesFree.closeGF Q :=
        funext fun x => (closeGFH.2 (hint 24) Q x).symm
      have cell : TabL.cells L 350 = TabL.close L 24 := table_head _ _ _ _ 13 (by omega)
      simp only []
      rw [table350, cell]
      unfold TabL.close
      rw [closing]
      simp only [same]
  rw [if_neg atClose]
  by_cases atCalls : n = 340
  · subst atCalls
    rw [if_pos rfl]
    have table340 : cellsH hint L 340 = TabL.lookCalls L 24 := by
      unfold cellsH
      rw [if_pos (Or.inr (by omega))]
      exact table_head _ _ _ _ 3 (by omega)
    cases site : L.look 24 false with
    | none => exact cellsH2_eq hint L 340
    | some s =>
      have same : callsGL s.1 s.2 = ProofFile.Honest.K3.Law.AtThr.callsG s.1 s.2 :=
        funext fun a => callsGL_eq _ _ a
      simp only []
      rw [table340]
      unfold TabL.lookCalls
      rw [site]
      simp only [same]
  rw [if_neg atCalls]
  exact cellsH2_eq hint L n

/-- The run of k members from m on, over these cells at LWn X. -/
noncomputable def runOverLightTail (hint : Nat → List (Nat × Nat)) (X : Verify.Public) (m k : Nat)
    (a : ShA) : Except String ShA :=
  (firstZA (fun n => (lightTailCells hint (LWn X) n).1)
    fun n => (lightTailCells hint (LWn X) n).2).runFrom m k a

/-- **It is `runH`.** -/
theorem runOverLightTail_eq (hint : Nat → List (Nat × Nat)) (X : Verify.Public) (m k : Nat)
    (a : ShA) : runOverLightTail hint X m k a = runH hint X m k a :=
  runFrom_congr (funext fun n => congrArg Prod.fst (lightTailCells_eq hint _ n))
    (funext fun n => congrArg Prod.snd (lightTailCells_eq hint _ n)) m k a

/-- The same as an equation of functions. -/
theorem runOverLightTail_fun : runOverLightTail = runH := by
  funext hint X m k a
  exact runOverLightTail_eq hint X m k a

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.lightTailCells
#print axioms Johnson.AtFull.Shape.lightTailCells_eq
#print axioms Johnson.AtFull.Shape.runOverLightTail
#print axioms Johnson.AtFull.Shape.runOverLightTail_eq
#print axioms Johnson.AtFull.Shape.runOverLightTail_fun
