-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Up.lean: the shared chain's shape (Johnson/Desc/K14/Shape/Lin.lean): THE LAW
ON SHAPES: UNDER PlanFacts AND THE TWO SENDINGS' TEST ON THE PLAN, at every shape, whether a run
reaches it or not, the test at a border (Facts.lean: factsB) is handed on by the update (Run.lean:
updS), from 1 to 8. No state, round or proof is named in it. What is made of it, under the same
premises: the updates, laid one behind the other from a shape that passes the test at 1, pass the
test at every border up to 9 (Johnson/Desc/K14/Shape/End.lean: facts_upTo). In this file nothing is
run, and nothing here can fail to return: updS is a total function.

How. Every shape is a state's shape: lift lays a state with the given shape, and sh2_lift says that
the reader undoes it. Block.Fits reads no state, and there are rounds and columns that pass it at
each of the eight (off the run of steps of the written example: steps_twins_met,
Johnson/Desc/K14/Honest/StepsTwins.lean); seven are spent here: at "SPLIT" the law is Run.lean's
state9_up. So Run.lean's laws on states, spent at lift a, speak of a. sh2_lift IS TRUE BECAUSE EACH
FIELD OF Sh2 IS READ OFF ITS OWN LEAF OF THE STATE: a component that is made from the constraints'
summands has no such law, and stands beside Sh2 (Johnson/Desc/K14/Shape/Mark.lean).

Main names:
  orcLift, grpLift, treeLift, lift   a state with a given shape: every field element that is written
                      here is 0, but a seed's factor, which is 1; as many default sample constraints
                      as the shape counts; a constraint of each listed kind, without a summand;
                      default values for a root that is handed in
  orc_lift, grp_lift, tree_lift, map_undo, sh2_lift   **every shape is a state's shape**
  lift_seeds          no seed of that state's key has the factor 0
  state_up            **under the premises below, the facts' half is handed on by the update, at
                      every shape**, from 1 to 7
  facts_up            **under the premises below, the whole test is handed on by the update, at
                      every shape and every border from 1 to 8**

What is assumed, as premises, at state_up and facts_up: PlanFacts (Run.lean's head spells it out);
the two sendings' test on the plan (planOkOwn); Eight P, which is taken so that the steps can be
named: that the eight are there follows from PlanFacts' clause on what goes out with o_u, by the
library's blocks_eight (Johnson/Desc/K14/Law/BlocksEight.lean), which is not called here. At
sh2_lift and the other laws on lift: nothing.

What is not claimed. lift a is no state that a run reaches; nothing is said of it but its shape and
its seeds' factors. That the test is needed. Nothing on soundness, on completeness or on hiding.
-/
import Johnson.Desc.K14.Shape.Run
import Johnson.Desc.K14.Honest.StepsTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (step_iff)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Own (allZero)
open VerifiableInference.Desc.K1 (planOkOwn)
open Desc.K14.Law (parU parO)
open Desc.K14.Honest (Eight PlanFacts steps_twins_met)

/-! ## A state with a given shape -/

/-- A message with the given shape: its sample constraints are as many default ones. -/
def orcLift (x : OrcSh) : Oracle :=
  { shape := x.shape, sampled := x.sampled, sampleRows := Array.replicate x.rows default
    pad := x.pad, groups := x.groups, ledger := x.ledger, spentAsMask := x.spent }

/-- A group with the given shape: a constraint of each listed kind, without a summand. -/
def grpLift (G : GrpSh) : Group :=
  { code := G.code, maskCode := G.maskCode, members := G.members.toArray, kept := G.kept.toArray
    rows := (G.kinds.map fun k => ({ kind := k } : Row)).toArray, inRun := G.inRun }

/-- A tree with the given shape: a root that is handed in has default values. -/
def treeLift (T : TreeSh) : Tree :=
  { shape := T.shape, number := T.number
    src := match T.src with
      | .own n => .own n
      | .given => .given default default
    parts := T.parts.toArray, oneList := T.oneList, lists := T.lists }

/-- **A state with the given shape**: every field element that is written here is 0, but a seed's
factor, which is 1; no column is left to read (opened := []); the rest, the key's item among them,
are the types' default values. -/
def lift (a : Sh2) : St :=
  { st := { codes := a.core.st.codes, oracles := (a.core.st.oracles.map orcLift).toArray
            groups := (a.core.st.groups.map grpLift).toArray }
    book := { trees := (a.core.book.trees.map treeLift).toArray
              place := a.core.book.place.toArray }
    roots := a.core.roots, opened := []
    loc := { psiSh := List.replicate a.lin.psi zeroE, gU := a.lin.gU, gOmega := a.lin.gOmega
             oU := { oracle := a.lin.oU, lay := a.lin.lay }, firstMask := a.lin.firstMask
             oOmega := a.lin.oOmega, oSp := a.lin.oSp, zFd := List.replicate a.lin.zFd zeroE
             key := { record := Array.replicate a.lin.record zeroE
                      seeds := a.lin.seeds.map fun n => ⟨List.replicate n zeroE, oneE⟩ } } }

/-- The reader undoes orcLift. -/
theorem orc_lift (x : OrcSh) : orcSh (orcLift x) = x := by
  cases x
  simp [orcSh, orcLift]

/-- The reader undoes grpLift. -/
theorem grp_lift (G : GrpSh) : grpSh (grpLift G) = G := by
  cases G
  simp [grpSh, grpLift, Function.comp_def]

/-- The reader undoes treeLift. -/
theorem tree_lift (T : TreeSh) : treeSh (treeLift T) = T := by
  obtain ⟨s, n, src, p, o, l⟩ := T
  cases src <;> simp [treeSh, treeLift, srcSh]

/-- A map that undoes another: a general law on lists. -/
theorem map_undo {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) (l : List α) :
    (l.map f).map g = l := by
  rw [List.map_map]
  exact (List.map_congr_left fun x _ => h x).trans (List.map_id l)

/-- **EVERY SHAPE IS A STATE's SHAPE.** -/
theorem sh2_lift (a : Sh2) : sh2 (lift a) = a := by
  obtain ⟨⟨⟨codes, os, gs⟩, ⟨ts, pl⟩, roots⟩, lin⟩ := a
  have e1 : ((os.map orcLift).toArray).toList.map orcSh = os := map_undo _ _ orc_lift os
  have e2 : ((gs.map grpLift).toArray).toList.map grpSh = gs := map_undo _ _ grp_lift gs
  have e3 : ((ts.map treeLift).toArray).toList.map treeSh = ts := map_undo _ _ tree_lift ts
  have e4 : linSh (lift ⟨⟨⟨codes, os, gs⟩, ⟨ts, pl⟩, roots⟩, lin⟩).loc = lin := by
    cases lin
    simp [linSh, lift, Function.comp_def]
  show Sh2.mk (CoreSh.mk (StSh.mk codes (((os.map orcLift).toArray).toList.map orcSh)
    (((gs.map grpLift).toArray).toList.map grpSh))
    (BookSh.mk (((ts.map treeLift).toArray).toList.map treeSh) pl.toArray.toList) roots) _ = _
  rw [e1, e2, e3, e4]

/-- No seed of that state's key has the factor 0. -/
theorem lift_seeds (a : Sh2) : ((lift a).loc.key.seeds.all (!allZero ·.beta)) = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨n, _, rfl⟩ := List.mem_map.1 hx
  rfl

/-! ## The law on shapes -/

variable {P : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **THE FACTS' HALF OF THE TEST IS HANDED ON BY THE UPDATE, AT EVERY SHAPE, FROM 1 TO 7, UNDER
PlanFacts (hP) AND THE TWO SENDINGS' TEST ON THE PLAN (hBU, hBO)**, at the eight of B (Eight P): no
state is named. -/
theorem state_up (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (B : Eight P)
    (a : Sh2) :
    (stateB P 1 a = true → stateB P 2 (updS P sentU 1 a) = true) ∧
    (stateB P 2 a = true → stateB P 3 (updS P sentU 2 a) = true) ∧
    (stateB P 3 a = true → stateB P 4 (updS P sentU 3 a) = true) ∧
    (stateB P 4 a = true → stateB P 5 (updS P sentU 4 a) = true) ∧
    (stateB P 5 a = true → stateB P 6 (updS P sentU 5 a) = true) ∧
    (stateB P 6 a = true → stateB P 7 (updS P sentU 6 a) = true) ∧
    (stateB P 7 a = true → stateB P 8 (updS P sentU 7 a) = true) := by
  obtain ⟨W, D, -, u, -⟩ := steps_twins_met P sentU layO hP hBU hBO B
    (fun _ _ _ => 0) ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
    ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
    ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩
    ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩ 0
  obtain ⟨c1, n1, s1⟩ := u.front.front.front.front.front.front.front.s1
  obtain ⟨c2, n2, s2⟩ := u.front.front.front.front.front.front.s2
  obtain ⟨c3, n3, s3⟩ := u.front.front.front.front.front.s3
  obtain ⟨c4, s4⟩ := u.front.front.front.front.s4
  obtain ⟨c5, n5, s5⟩ := u.front.front.front.s5
  obtain ⟨c6, n6, s6⟩ := u.front.front.s6
  obtain ⟨c7, n7, s7⟩ := u.front.s7
  have e := sh2_lift a
  refine ⟨fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_, fun g => ?_,
    fun g => ?_⟩
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).1 (by rw [e]; exact g)
      ((step_iff _ _ _ _ _ _ _).1 s1).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).1 hs, e] at gx
    exact gx
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).2.1 (by rw [e]; exact g)
      ((step_iff _ _ _ _ _ _ _).1 s2).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).2.1 hs, e] at gx
    exact gx
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).2.2.1 (by rw [e]; exact g)
      (lift_seeds a) ((step_iff _ _ _ _ _ _ _).1 s3).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).2.2.1 hs, e] at gx
    exact gx
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).2.2.2.1 (by rw [e]; exact g)
      ((step_iff _ _ _ _ _ _ _).1 s4).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).2.2.2.1 hs, e] at gx
    exact gx
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).2.2.2.2.1
      (by rw [e]; exact g) ((step_iff _ _ _ _ _ _ _).1 s5).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).2.2.2.2.1 hs, e] at gx
    exact gx
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).2.2.2.2.2.1
      (by rw [e]; exact g) ((step_iff _ _ _ _ _ _ _).1 s6).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).2.2.2.2.2.1 hs, e] at gx
    exact gx
  · obtain ⟨d', hs, gx⟩ := (state_next hP hBU hBO B 0 (lift a) _ _).2.2.2.2.2.2.1
      (by rw [e]; exact g) ((step_iff _ _ _ _ _ _ _).1 s7).1
    rw [(stepCarries (sentU := sentU) hP.goes hP.two B 0 _ _ _ _ _).2.2.2.2.2.2.1 hs, e] at gx
    exact gx

/-- **THE WHOLE TEST IS HANDED ON BY THE UPDATE, AT EVERY SHAPE AND EVERY BORDER FROM 1 TO 8, UNDER
PlanFacts (hP) AND THE TWO SENDINGS' TEST ON THE PLAN (hBU, hBO)**, at the eight of B (Eight P). -/
theorem facts_up (hP : PlanFacts P.par P.codes sentU layO)
    (hBU : planOkOwn (parU P sentU) = true) (hBO : planOkOwn (parO P) = true) (B : Eight P)
    (a : Sh2) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) (h : factsB P b a = true) :
    factsB P (b + 1) (updS P sentU b a) = true := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := state_up hP hBU hBO B a
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := kinds_up (P := P) (sentU := sentU) a
  obtain ⟨gs, gk⟩ := (factsB_iff P b a).1 h
  refine (factsB_iff P (b + 1) _).2 ?_
  match b, h1, h8, gs, gk with
  | 1, _, _, gs, _ => exact ⟨u1 gs, fun _ => k1⟩
  | 2, _, _, gs, gk => exact ⟨u2 gs, fun _ => k2 (gk (by omega))⟩
  | 3, _, _, gs, gk => exact ⟨u3 gs, fun _ => k3 gs (gk (by omega))⟩
  | 4, _, _, gs, gk => exact ⟨u4 gs, fun _ => k4 gs (gk (by omega))⟩
  | 5, _, _, gs, gk => exact ⟨u5 gs, fun _ => k5 (gk (by omega))⟩
  | 6, _, _, gs, gk => exact ⟨u6 gs, fun _ => k6 (gk (by omega))⟩
  | 7, _, _, gs, gk => exact ⟨u7 gs, fun _ => k7 (gk (by omega))⟩
  | 8, _, _, gs, gk => exact ⟨state9_up a gs, fun _ => k8 gs (gk (by omega))⟩

end Desc.K14.Shape

#print axioms Desc.K14.Shape.orc_lift
#print axioms Desc.K14.Shape.grp_lift
#print axioms Desc.K14.Shape.tree_lift
#print axioms Desc.K14.Shape.map_undo
#print axioms Desc.K14.Shape.sh2_lift
#print axioms Desc.K14.Shape.lift_seeds
#print axioms Desc.K14.Shape.state_up
#print axioms Desc.K14.Shape.facts_up
