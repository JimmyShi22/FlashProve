-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/JoinPans.lean: CONDITIONAL: the tie of pans_of_B (PansB.lean) to
the structure StackPub of Johnson/Desc/First/K4/Returns/Stack.lean, and to the field stack of
HearPub (Johnson/Desc/First/K4/Returns/Whole.lean) at the environment that the hearing lays.

Limits. THE FIELD join OF StackPub STAYS A PREMISE. No file of this folder proves the test pansB
true at any plan. #guard is Lean's evaluator and gives no proof. PansBTest.lean [not in this
library; so here read: not tested in this library] evaluates it at the
small synthetic plan; no file of this folder evaluates it at a model's plan. No property is claimed.

  stackPub_of_B   StackPub from the test and JoinPub.
  stack_of_B      the field stack of HearPub, from the test at the blank environment and JoinPub.
-/
import Johnson.Desc.First.K4.Returns.Whole
import Johnson.Desc.First.K4.Returns.Pub.PansB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Total (EnvSkel)

/-- The environment that the hearing lays, and the blank one. -/
theorem envOf_skel (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (iU3 : Nat)
    (tab : List TableAt) : EnvSkel (Rt.envOf P hp g fo iU3 tab) (blankEnv P hp g iU3 tab) :=
  ⟨rfl, rfl, rfl⟩

/-- **StackPub from the test and JoinPub.** -/
theorem stackPub_of_B {P : Pub} {v v₀ : Env} (S : EnvSkel v v₀) {lamS NCLp : Nat}
    (h : pansB P v₀ lamS NCLp = true) (H : Heard) (hj : Rt.JoinPub v H.fo) :
    Rt.StackPub P v H lamS NCLp :=
  ⟨pans_of_B S h H, hj⟩

/-- **The field stack of HearPub**, to the letter. -/
theorem stack_of_B {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {ztF : Array E}
    {iU3 : Nat} {tab : List TableAt}
    (h : pansB P (blankEnv P hp g iU3 tab) hp.lamS (Rt.nclp hp g) = true)
    (hj : Rt.JoinPub (Rt.envOf P hp g fo iU3 tab) fo) :
    ∀ H : Heard, H.fo = fo → H.ztF = ztF →
      Rt.StackPub P (Rt.envOf P hp g fo iU3 tab) H hp.lamS (Rt.nclp hp g) :=
  fun H e _ => stackPub_of_B (envOf_skel P hp g fo iU3 tab) h H (e ▸ hj)

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.envOf_skel
#print axioms OnBytes.Desc.First.K4.RtPub.stackPub_of_B
#print axioms OnBytes.Desc.First.K4.RtPub.stack_of_B
