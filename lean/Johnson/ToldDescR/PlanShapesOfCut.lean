-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/PlanShapesOfCut.lean: THE TEST ON THE PLAN `PlanShapes`
(Johnson/ToldDescR/BookAtW.lean: the listed shape number z is what the description tells of the tree
ft + z) AT THE WRITTEN LIST `LFull` (Johnson/HB/LLHARD/LaidWritten.lean), ft := 0 AND EVERY n₁, FOR
EVERY DESCRIPTION WHOSE FIRST CHAIN's CUT INTO SUB-PROTOCOLS IS THE WRITTEN ONE
(`cutOf F.first.blocksInOrder = cutFirstFull`, Johnson/Desc/Ok/PlanWritten/CutTest.lean).

How. A row of the cut holds all that its sub-protocol tells (`toldRounds_flat`): so what the first
chain tells, in a row, is a closed list, and the comparison with `LFull.shapes` is a closed fact,
which Lean's kernel evaluates.

  `oraclesOf_cut`: what a list of sub-protocols tells, off its cut's rows.
  `toldFirstFull`: what the written cut's rows tell. `told_first_len`: of 83 trees.
  `shapes_fit_written`: AT EACH z < 83 a shape is listed, something is told, and `shapeIsB` accepts:
    by the kernel. `shapes_can_fail`: the negative test: against the list without its first shape
    the test rejects.
  **`planShapes_of_cut`**: the statement.
Limits. That a description has the written cut is a premise (a row of the proof file's entry tests
in an older list of 13 rows asks it). The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.ToldDescR.BookAtW
import Johnson.Desc.Ok.PlanWritten.CutTestLaws
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldRounds toldRounds_flat)
open VerifiableInference.Desc.K13.Law (LFull laid_sizes)

/-- What a list of sub-protocols tells, off its cut's rows. -/
theorem oraclesOf_cut {S Cl : Type} (bs : List (Block S Cl)) :
    oraclesOf bs = (cutOf bs).flatMap fun r => r.2.2.2.2.1.flatMap (·.2) := by
  unfold oraclesOf cutOf
  rw [List.flatMap_map]
  refine List.flatMap_congr fun b _ => ?_
  show b.oracles.flatMap id = (toldRounds b).flatMap (·.2)
  rw [toldRounds_flat, List.flatMap_id]

/-- What the written cut's rows tell, in a row. -/
def toldFirstFull : List Oracle := cutFirstFull.flatMap fun r => r.2.2.2.2.1.flatMap (·.2)

set_option maxRecDepth 1000000 in
theorem told_first_len : toldFirstFull.length = 83 := by decide +kernel

/-- The comparison, with both sides asked to be there. -/
def fitAllB (shapes : List OnBytes.TreeShape) (told : List Oracle) (n : ℕ) : Bool :=
  (List.range n).all fun z =>
    match shapes[z]?, told[z]? with
    | some tsh, some o => shapeIsB tsh o
    | _, _ => false

set_option maxRecDepth 1000000 in
/-- **At each of the 83 trees the listed shape is what the written cut tells.** -/
theorem shapes_fit_written : fitAllB LFull.shapes toldFirstFull 83 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test. -/
theorem shapes_can_fail : fitAllB LFull.shapes.tail toldFirstFull 82 = false := by decide +kernel

/-- **`PlanShapes` at the written list, wherever the first chain's cut is the written one.** -/
theorem planShapes_of_cut {Xi : Type} (F : FileDescription Xi)
    (h : cutOf F.first.blocksInOrder = cutFirstFull) (n₁ : ℕ) : PlanShapes F LFull 0 n₁ := by
  intro z _ tsh o h1 h2
  have hz : z < 83 := by
    have := (List.getElem?_eq_some_iff.1 h1).1
    rwa [laid_sizes.2.2.1] at this
  have e : F.oracleAt (0 + z) = toldFirstFull[z]? := by
    unfold FileDescription.oracleAt
    rw [Nat.zero_add, oraclesOf_cut F.first.blocksInOrder, h, List.append_assoc]
    exact List.getElem?_append_left (show z < toldFirstFull.length by rw [told_first_len]; exact hz)
  have k := List.all_eq_true.1 shapes_fit_written z (List.mem_range.2 hz)
  rw [h1, ← e, h2] at k
  exact (shapeIs_iff _ _).1 k

end ToldDesc

#print axioms ToldDesc.oraclesOf_cut
#print axioms ToldDesc.told_first_len
#print axioms ToldDesc.shapes_fit_written
#print axioms ToldDesc.shapes_can_fail
#print axioms ToldDesc.planShapes_of_cut
