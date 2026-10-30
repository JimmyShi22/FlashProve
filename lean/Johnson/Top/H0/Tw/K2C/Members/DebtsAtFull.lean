-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Members/DebtsAtFull.lean: code switching (the kind K2): EXAMPLES AND NEGATIVE
TESTS for Johnson/Top/H0/Tw/K2C/KeptPosAt.lean and GroupAtNums.lean, at the request's shape of the
full-size example as a written value (`shapeFull`, Johnson/Desc/ReqLit/Full.lean). Closed facts, by
an evaluation in Lean's kernel. No sub-protocol imports this file.

The premises on the public shape can be met at the full size:
  full_ok          `reqShapeOk shapeFull = true` (KeptPosAt's hok)
  full_links       `shapeFull` has 25 links (GroupAtNums' hlen, at the written value)
What follows is not empty:
  full_kept        how many kept members the 26 groups' targets have: none, then twelve times two
                   and one, then none: 36 in all. At the first and the last group there is no kept
                   member: there `KeptPos` says nothing
  full_keptPos     `KeptPos` at every group's target, by the law `keptPos_group`
  full_test        the same by the test with code `K2Hands.keptPosB`
  prepFull · nums_answer   at the written sizes `proofSizedFull`, with what `prepareAt` makes of
                   them (its text but for the tie; the sub-proofs' open rows left empty): `numsAt`
                   answers at all 25 places, and n.grp is 1, 2, …, 25: the binder of `hgrp_link` and
                   `hgrp_finish` is idle at none of them
  frameGroupsB · groups_of_test   KeptPosAt's premise hgroups as a test with code on a frame, and
                   that its accept gives the premise: for a run that asks it at a state
Negative tests:
  nums_none        at link 0 and at link 26 `numsAt` answers nothing: no switch stands there
  shapeBent        `shapeFull` with the main rows of every message that later links read set to 0
  bent_not_ok      `reqShapeOk shapeBent = false`: the premise hok fails
  bent_fails       `keptPosB` rejects at a group of `shapeBent`
  bent_not_keptPos   so `KeptPos` is false at a group's target there: the law's end fails with hok
  small_links      the small example's shape has 5 links, not 25
  finish_bent      where the shape that `prepOf` holds has not 25 links, the equation at the finish
                   at segment number 25 is FALSE: so hlen cannot be dropped

Limits. THE FACTS SPEAK OF THE WRITTEN VALUE: that it is the planner's request at the shipped public
files is held by a run outside the library (Full.lean's own head). Nothing on a state of the
verifier: hshape and hgroups are not met here. `nums_answer` is at the written sizes and at empty
open rows: its P is not shown to be a value of `prepOf`. No soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.Tw.K2C.KeptPosAt
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Desc.ReqLit.Full
import Johnson.Desc.ReqLit.Small
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2.Members
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (Numbers ModelPart)
open VerifiableInference.Desc.First.K2 (KeptPos keptPos_group keptPosB_of_keptPos)
open VerifiableInference.Desc.First.K2Hands (keptPosB)
open VerifiableInference.Desc.ReqLit (shapeFull shapeSmall shapeFull_ok)
open VerifiableInference.PlanWritten (proofSizedFull)

theorem full_ok : reqShapeOk shapeFull = true := shapeFull_ok

theorem full_links : shapeFull.link.length = 25 := by decide +kernel

theorem full_kept : (reqGroups shapeFull).toList.map (·.target.kept.size) =
    0 :: ((List.replicate 12 [2, 1]).flatten ++ [0]) := by decide +kernel

theorem full_keptPos {l : Nat} {G : ReqGroup} (h : (reqGroups shapeFull)[l]? = some G) :
    KeptPos G.target := keptPos_group full_ok h

theorem full_test : ((reqGroups shapeFull).all fun G => keptPosB G.target) = true := by
  decide +kernel

/-- A group as a value that can be compared: its four fields. -/
def groupKey (G : ReqGroup) : Nat × Nat × SwitchTarget × Array (Nat × Nat) :=
  (G.k, G.h, G.target, G.born)

theorem groupKey_inj {G G' : ReqGroup} (h : groupKey G = groupKey G') : G = G' := by
  cases G
  cases G'
  simp only [groupKey, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The frame's groups are those of its shape: with code. -/
def frameGroupsB (f : ReqFrame) : Bool :=
  decide (f.groups.toList.map groupKey = (reqGroups f.shape).toList.map groupKey)

theorem groups_of_test {f : ReqFrame} (h : frameGroupsB f = true) :
    f.groups = reqGroups f.shape :=
  Array.toList_inj.1 ((List.map_inj_right fun _ _ => groupKey_inj).1 (of_decide_eq_true h))

/-- What `prepareAt` makes of the written sizes: its text but for the tie. -/
def prepFull (sub : Subproofs) : Option Prep :=
  ((List.range proofSizedFull.request.link.length).mapM
    (treesOfLink proofSizedFull.codes
      { shape := proofSizedFull.request, groups := reqGroups proofSizedFull.request })).map
    fun trees => ⟨proofSizedFull, Plan.framesOf proofSizedFull sub, trees⟩

/-- Sub-proofs with no open row. -/
def subNone : Subproofs :=
  { links := [], openRows := [], plan := fun _ _ => pure (), pendingRows := 0, matrixRows := 0 }

/-- The links of the 25 places of a switch: 1, …, 24, and none at the finish. -/
def switchLinks : List (Option Nat) := (List.range 24).map (fun i => some (i + 1)) ++ [none]

set_option maxRecDepth 1000000 in
theorem nums_answer : (prepFull subNone).map (fun P => switchLinks.map fun k =>
    (numsAt P k).map (·.grp)) = some ((List.range 25).map fun i => some (i + 1)) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem nums_none : (prepFull subNone).map (fun P =>
    ((numsAt P (some 0)).isSome, (numsAt P (some 26)).isSome)) = some (false, false) := by
  decide +kernel

/-- A link with the main rows of every message that later links read set to 0. -/
def bendLink (L : ReqLink) : ReqLink :=
  { L with messages := L.messages.map fun m =>
      if m.life == 0 then m else { m with shape := { m.shape with mainRows := 0 } } }

/-- The negative test's shape. -/
def shapeBent : ReqShape := { shapeFull with link := shapeFull.link.map bendLink }

theorem bent_not_ok : reqShapeOk shapeBent = false := by decide +kernel

theorem bent_fails : ((reqGroups shapeBent).all fun G => keptPosB G.target) = false := by
  decide +kernel

theorem bent_not_keptPos : ¬ ∀ G ∈ (reqGroups shapeBent).toList, KeptPos G.target := by
  intro h
  have e : ((reqGroups shapeBent).all fun G => keptPosB G.target) = true := by
    rw [Array.all_eq_true_iff_forall_mem]
    exact fun G hG => keptPosB_of_keptPos (h G (Array.mem_toList_iff.2 hG))
  rw [bent_fails] at e
  cases e

theorem small_links : shapeSmall.link.length = 5 := by decide +kernel

/-- Without 25 links the equation at the finish is false. -/
theorem finish_bent {St Cl : Type} (ps : List P5T.PSeat) (sh : ReqShape) (links : List ModelPart)
    (bs : List (Block St Cl)) {P : Prep} {n : Nums} (h : numsAt P none = some n)
    (hne : P.z.request.link.length ≠ 25) :
    ((P5T.numbersOf ps).atBlocks sh links bs).groupAt 25 ≠ n.grp := by
  rw [numsAt_grp h]
  exact fun e => hne e.symm

end P1K2.Members

#print axioms P1K2.Members.full_links
#print axioms P1K2.Members.full_kept
#print axioms P1K2.Members.full_keptPos
#print axioms P1K2.Members.full_test
#print axioms P1K2.Members.groups_of_test
#print axioms P1K2.Members.nums_answer
#print axioms P1K2.Members.nums_none
#print axioms P1K2.Members.bent_not_ok
#print axioms P1K2.Members.bent_fails
#print axioms P1K2.Members.bent_not_keptPos
#print axioms P1K2.Members.small_links
#print axioms P1K2.Members.finish_bent
