-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchBools.lean: THE PREMISES OF THE RUNS OF CLAIMS THAT HAVE A RunLaw, AS
Bools OF THE STATE (RunLawB, BatchFrames.lean): what the batching member's one Bool batchV is made
of. Definitions with code, and the laws that a yes gives the premise. Nothing is evaluated.

  `RunLawB.ofImp`: THE PATTERN: a RunLaw whose pre IS P, and a Bool V whose yes gives P.
  THE Bools THEMSELVES ARE THEIR HOUSES' WHERE ONE LIES: "K8.equations": eqPreB
    (Johnson/Desc/K8/Honest/EqAllBools.lean) · K4's "front" and "back": planEnvB
    (Johnson/Desc/First/K4/Returns/RunBools.lean).
  `endsS`, `endsS_pays`: the output head's four runs: Ends (Johnson/Desc/K6/Shape/Core.lean) as a
    Bool of the state: typed here: none lay.
  K5's four: preK5 A IS "valsTS A s = true" (another house's Bool). K11's: True.
  **`k8B`**, **`k4B`**, **`k5B`**, **`k6B`**, **`k11B`**: for ANY RunLaw with that pre: its RunLawB.

Limits. That a Bool accepts at a state of a run is not shown. A yes SUFFICES for the premise; the
way back is not stated. A RunLawB is data: the Bool that always says no meets it for every RunLaw:
so all that counts is which Bool each of these lays. The lookup's three runs have no Bool here: for
"objects", "guests" and, at the head's link, "planes" it is the one that always accepts
(BatchSlotsK3.lean); for "planes" at the attention links it is valsTS A (BatchCellsAtt.lean).
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchFrames
import Johnson.Desc.K8.Honest.EqAllBools
import Johnson.Desc.First.K4.Returns.RunBools
import Johnson.Desc.K5.Honest.Law.RunsLaw
import Johnson.Desc.K6.Shape.Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest (EqPre eqPreB eqPre_of_B)
open OnBytes.Desc.First.K4.Rt (PlanEnv planEnvB planEnv_of_B)
open VerifiableInference.Desc.Kinds.Head.Shape (Ends endsB)
open H2K5.Honest (preK5 valsTS)
open VerifiableInference.Desc.K9.Shape

/-- **THE PATTERN.** -/
def RunLawB.ofImp {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run)
    (V : Nat → S → Bool) (P : Nat → S → Prop) (h : R.pre = P)
    (hp : ∀ n s, V n s = true → P n s) : RunLawB R where
  preB := V
  pays := fun n s hv => by rw [h]; exact hp n s hv

/-! ## K8 -/

def k8B {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run)
    (h : R.pre = fun _ s => EqPre s) : RunLawB R :=
  RunLawB.ofImp R (fun _ s => eqPreB s) _ h fun _ _ hv => eqPre_of_B hv

/-! ## K6 -/

/-- Ends as a Bool of the state. Where no lookup's record is laid it says yes, as Ends holds emptily
there. -/
def endsS (p : VerifiableInference.Desc.Kinds.Head.Par) (s : S) : Bool :=
  (s.lookHeard?.map (endsB p)).getD true

theorem endsS_pays {p : VerifiableInference.Desc.Kinds.Head.Par} {s : S}
    (h : endsS p s = true) : Ends p s := by
  refine ⟨fun g hg => ?_⟩
  unfold endsS at h
  rw [hg] at h
  exact h

def k6B {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run)
    (p : VerifiableInference.Desc.Kinds.Head.Par) (h : R.pre = fun _ s => Ends p s) : RunLawB R :=
  RunLawB.ofImp R (fun _ s => endsS p s) _ h fun _ _ hv => endsS_pays hv

/-! ## K4 -/

def k4B {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run) (P : Layer.Pub)
    (h : R.pre = fun _ s => PlanEnv P s) : RunLawB R :=
  RunLawB.ofImp R (fun _ s => planEnvB P s) _ h fun _ _ hv => planEnv_of_B hv

/-! ## K5, K11 -/

def k5B {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run) (A : Attention.Plan)
    (h : R.pre = preK5 A) : RunLawB R :=
  RunLawB.ofImp R (fun _ s => valsTS A s) _ h fun _ _ hv => hv

def k11B {run : VerifiableInference.Desc.K9.Shape.Run} (R : RunLaw run)
    (h : R.pre = fun _ _ => True) : RunLawB R :=
  RunLawB.ofImp R (fun _ _ => true) _ h fun _ _ _ => trivial

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.endsS_pays
#print axioms Johnson.AtFull.Shape.k8B
#print axioms Johnson.AtFull.Shape.k6B
#print axioms Johnson.AtFull.Shape.k4B
#print axioms Johnson.AtFull.Shape.k5B
#print axioms Johnson.AtFull.Shape.k11B
#print axioms Johnson.AtFull.Shape.RunLawB.ofImp
#print axioms Johnson.AtFull.Shape.endsS
