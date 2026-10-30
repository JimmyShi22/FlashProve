-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/ShapeIsCut.lean: the shape that `ProofFile.shapeOf` returns at the written table of
stretches and the written 25 kinds IS THE LIST OF THE 358 NAMES AND PLACES OF THE WRITTEN CUT
(`PlanWritten.cutFirstFull`, Johnson/Desc/Ok/PlanWritten/CutLit.lean). No new written value.

  `shapeW`: the written cut's names and places. `shapeMade`: what `shapeOf` returns there.
  `shape_is`: one closed statement by an evaluation in Lean's kernel; `shape_bent`: against the
    written list less its last row the test says no (bends inside the list: ShapeIsCutNo.lean).
  `shapeOf_written`: under the two premises hc and hk: **shapeOf Z = .ok shapeW.**

Limits. IT PAYS NEITHER `Z.cuts = cutWritten` NOR `subsOf Z = subsW`: premises. No soundness is
claimed.
-/
import Johnson.AtFull.Desc.ShapeAtWritten
import Johnson.Desc.Ok.PlanWritten.CutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Desc
open ProofFile
open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.First (ModelPart kindsBeforeBatching)
open VerifiableInference.PlanWritten (cutFirstFull)
open Johnson.AtFull.Cut (cutWritten)

/-- The written shape: the names and places of the written cut's 358 rows. -/
def shapeW : List (String × Place) := cutFirstFull.map fun r => (r.1, r.2.1)

/-- What shapeOf returns there, as an option. -/
def shapeMade : Option (List (String × Place)) :=
  (chainC (idleOf spotsWritten) subsW (Frames.unguarded : Frames Unit Unit)).toOption.map
    fun c => c.blocksInOrder.map fun b => (b.name, b.place)

set_option maxHeartbeats 0 in
theorem shape_is : decide (shapeMade = some shapeW) = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem shape_bent : decide (shapeMade = some shapeW.dropLast) = false := by decide +kernel

/-- **Where the table of stretches and the 25 kinds are the written ones (hc, hk: premises), shapeOf
returns the written shape.** -/
theorem shapeOf_written {Z : Pub} (hc : Z.cuts = cutWritten) (hk : subsOf Z = subsW) :
    shapeOf Z = .ok shapeW := by
  obtain ⟨c, h₁, h₂⟩ := shape_written hc hk
  have e : shapeMade = some shapeW := of_decide_eq_true shape_is
  unfold shapeMade at e
  rw [h₁] at e
  rw [h₂]
  exact congrArg Except.ok (Option.some.inj e)

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.shape_is
#print axioms Johnson.AtFull.Desc.shape_bent
#print axioms Johnson.AtFull.Desc.shapeOf_written
