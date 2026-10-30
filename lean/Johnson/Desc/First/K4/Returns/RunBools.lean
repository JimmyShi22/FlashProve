-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/RunBools.lean: THE LAYERS' OWN ROUNDS (K4): THE PREMISE OF ITS TWO
RUNS OF CLAIMS ON SHAPES (PlanEnv, Johnson/Desc/First/K4/Returns/RunShape.lean) AS A Bool OF THE
STATE. Definitions with their laws; nothing is evaluated.

Why. PlanEnv is two equations: the environment of what was heard has the plan's layout and the
plan's table of scales. Whoever wants the premises of all runs of a batching as one test with code
wants each as a Bool with one lemma.

  Decidable equality is derived here, under this file's own namespace, for the layout, the table of
  scales and the eight records of plain data of which the layout is made: the files beneath this one
  have none for the layout or the table of scales.
  planEnvB P s    the two equations, decided, at what the state has heard; true where nothing is
                  heard, as PlanEnv is.
  **planEnvB_iff**   planEnvB P s = true just where PlanEnv P s.
  planEnv_of_B    the one direction, as a lemma of its own.

Limits. The Bool compares two whole layouts, tables among them: it is not meant for Lean's kernel at
the protocol's sizes. THE TEN DERIVED DECIDERS ARE GLOBAL INSTANCES: whoever imports this file
inherits them. For OnBytes.Model.Call and Forest.Shape the library derives such a pair in three more
files (Johnson/Desc/First/FillK4.lean, Johnson/Desc/First/Att/K05PublicB.lean,
Johnson/AtFull/Shape/ShapeDecEqL.lean). Where two of the four files are imported, which pair a bare
"decide" finds is Lean's choice. Each instance carries its proof, so nothing false follows. The
term, and what the kernel pays for it, can differ. The names of the ten in the "#print axioms" lines
are Lean's own make: instDecidableEqShape_johnson and …_johnson_1 do not tell which is
Forest.Shape's and which Layer.Shape's. Who shows that it accepts at a state of a run is not said
here: Johnson/Desc/First/K4/Returns/RunPays.lean has PlanEnv right behind K4's own yes. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.RunShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes
open OnBytes.Model.Layer (Pub)
open VerifiableInference.Desc.First (S)

/- Inside this file's own namespace, so that the instances' names meet nobody else's. The instances
themselves are global: every importer's search sees them (see the head's Limits). -/
deriving instance DecidableEq for OnBytes.Model.Call
deriving instance DecidableEq for OnBytes.Model.Forest.Shape
deriving instance DecidableEq for OnBytes.Model.TenAt
deriving instance DecidableEq for OnBytes.Model.Seg
deriving instance DecidableEq for OnBytes.Model.CallD
deriving instance DecidableEq for OnBytes.Model.Layer.KindD
deriving instance DecidableEq for OnBytes.Model.Layer.Ten
deriving instance DecidableEq for OnBytes.Model.Layer.Shape
deriving instance DecidableEq for OnBytes.Model.Layer.Scales
deriving instance DecidableEq for OnBytes.Model.Layer.Lay

/-- **The two runs' premise, with code.** -/
def planEnvB (P : Pub) (s : S) : Bool :=
  s.own?.all fun o => decide (o.v.y = P.y) && decide (o.v.sc = P.sc)

theorem planEnvB_iff (P : Pub) (s : S) : planEnvB P s = true ↔ PlanEnv P s := by
  unfold planEnvB PlanEnv
  cases s.own? with
  | none => exact ⟨fun _ o h => (nomatch h), fun _ => rfl⟩
  | some o =>
    constructor
    · intro h o' ho'
      obtain rfl : o = o' := Option.some.inj ho'
      have h' : (decide (o.v.y = P.y) && decide (o.v.sc = P.sc)) = true := h
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h'
      exact h'
    · intro h
      obtain ⟨h1, h2⟩ := h o rfl
      show (decide (o.v.y = P.y) && decide (o.v.sc = P.sc)) = true
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨h1, h2⟩

theorem planEnv_of_B {P : Pub} {s : S} (h : planEnvB P s = true) : PlanEnv P s :=
  (planEnvB_iff P s).1 h

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.planEnvB_iff
#print axioms OnBytes.Desc.First.K4.Rt.planEnv_of_B
#print axioms OnBytes.Desc.First.K4.Rt.planEnvB
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqLay_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqKindD_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqScales_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqCallD_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqSeg_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqShape_johnson_1
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqShape_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqCall_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqTenAt_johnson
#print axioms OnBytes.Desc.First.K4.Rt.instDecidableEqTen_johnson
