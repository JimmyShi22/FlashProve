-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/ShapeAtWritten.lean: `ProofFile.shapeOf Z` (Johnson/Desc/ProofFile/Frames1.lean)
returns where the table of stretches is the written one and the 25 segments' kinds are the written
ones.

`shapeOf` reads of Z its table of stretches (through `spotsOf`) and the kinds of its 25 built
segments (`subsOf`), and runs the driver's chain over one idle block a place.

  `idleOf`: one idle block a place: `shapeOf`'s own text. `shapeOf_of`: the general law.
  `subsW`: twelve times layers and attention, then the head.
  `chain_idle`, `chain_count`: closed statements by evaluations in Lean's kernel, at the written
    list of 282 places (`spotsWritten`, SpotsWritten.lean in this folder): the driver's chain over
    the idle blocks returns; its flat list has 358 blocks.
  `shape_written`: the return, under the two premises hc and hk.

Limits. IT PAYS NEITHER `Z.cuts = cutWritten` NOR `subsOf Z = subsW`: premises. No soundness is
claimed.
-/
import Johnson.AtFull.Desc.SpotsWritten
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Desc
open ProofFile
open VerifiableInference.Desc (Block Chain roundlessBlock)
open VerifiableInference.Desc.First (ModelPart)
open Johnson.AtFull.Cut (cutWritten)

/-- One idle block a place: shapeOf's own text. -/
def idleOf (ps : List Spot) : List (Block Unit Unit) :=
  ps.map fun p => { (roundlessBlock p.name 1 none 0 .ok : Block Unit Unit) with place := p.place }

/-- **Where its two steps return (q₁, hc: premises), shapeOf returns, and at which value.** -/
theorem shapeOf_of {Z : Pub} {ps : List Spot} {c : Chain Unit Unit}
    (q₁ : spotsOf Z.cuts = some ps)
    (hc : chainC (idleOf ps) (subsOf Z) Frames.unguarded = .ok c) :
    shapeOf Z = .ok (c.blocksInOrder.map fun b => (b.name, b.place)) := by
  have h : shapeOf Z = (chainC (idleOf ps) (subsOf Z) Frames.unguarded).bind fun c =>
      .ok (c.blocksInOrder.map fun b => (b.name, b.place)) := by
    unfold shapeOf
    rw [q₁]
    rfl
  rw [h, hc]
  rfl

/-- The 25 segments' kinds at the full size: twelve times layers and attention, then the head. -/
def subsW : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [ModelPart.head]

set_option maxHeartbeats 0 in
theorem chain_idle :
    (chainC (idleOf spotsWritten) subsW (Frames.unguarded : Frames Unit Unit)).isOk = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chain_count :
    ((chainC (idleOf spotsWritten) subsW (Frames.unguarded : Frames Unit Unit)).toOption.map
      (·.blocksInOrder.length)) = some 358 := by
  decide +kernel

/-- **Where the table of stretches and the 25 kinds are the written ones (hc, hk: premises), shapeOf
returns.** -/
theorem shape_written {Z : Pub} (hc : Z.cuts = cutWritten) (hk : subsOf Z = subsW) :
    ∃ c, chainC (idleOf spotsWritten) subsW (Frames.unguarded : Frames Unit Unit) = .ok c ∧
      shapeOf Z = .ok (c.blocksInOrder.map fun b => (b.name, b.place)) := by
  cases h : chainC (idleOf spotsWritten) subsW (Frames.unguarded : Frames Unit Unit) with
  | error e =>
    have := chain_idle
    rw [h] at this
    cases this
  | ok c =>
    refine ⟨c, rfl, shapeOf_of (ps := spotsWritten) ?_ ?_⟩
    · rw [hc]
      exact spots_written
    · rw [hk]
      exact h

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.shapeOf_of
#print axioms Johnson.AtFull.Desc.chain_idle
#print axioms Johnson.AtFull.Desc.chain_count
#print axioms Johnson.AtFull.Desc.shape_written
