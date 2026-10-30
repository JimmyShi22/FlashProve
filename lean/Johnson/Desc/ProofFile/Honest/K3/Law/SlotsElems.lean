-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SlotsElems.lean: the number of hidden values that the face of a
proof file's lookup counts (`Face.slots`, Johnson/Desc/First/Look/K3LookupGeneral.lean) is the number that
the verifier program's model counts for the shape (`Forest.elems`, OnBytes/Model/Forest.lean).
Without a hypothesis. Theorems.

Terms. Honest/K3/GLOSSARY.md ("face", "hidden value", "slot").

What is shown.
  `slots_elems`: the equation of the two numbers.
  `foldl_sum`, `layerSlots_eq`: helpers.

Users. The plan's test on the room of a lookup is stated at `Forest.elems`; the row of parts and its
theorems count by `Face.slots`. Under Honest/K3/ this file is imported by
Honest/K3/Good/Live/Unnamed.lean, Honest/K3/Good/Live/Windows.lean, Honest/K3/Law/Thread/Front.lean,
Honest/K3/Law/Thread/MemberDecides.lean and Honest/K3/Law/Thread/Out.lean.

Limits. An equation of two numbers.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open VerifiableInference.Desc.K3 (faceOf)
open OnBytes.Model (sumcheckSlots layerSlots roundValues)

/-- A sum written as a fold is the sum of the list. -/
theorem foldl_sum (g : Nat → Nat) : ∀ n,
    (List.range n).foldl (fun s i => s + g i) 0 = ((List.range n).map g).sum
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.map_append, List.sum_append, foldl_sum g n]
    simp

theorem layerSlots_eq (k : Nat) : layerSlots k = 2 * k + 5 := by
  show 1 + k * 2 + 2 + 2 = 2 * k + 5
  omega

/-- **The face of a proof file's lookup counts as many hidden values as the verifier program's model
does.** -/
theorem slots_elems (h : OnBytes.Model.Forest.Shape) :
    (faceOf h).slots = OnBytes.Model.Forest.elems h := by
  have e1 : (fun mu => layerSlots mu) = fun k => 2 * k + 5 := funext layerSlots_eq
  have e2 : (fun l => layerSlots (5 + l)) = fun l => 2 * (5 + l) + 5 :=
    funext fun l => layerSlots_eq (5 + l)
  unfold OnBytes.Model.Forest.elems
  rw [foldl_sum fun mu => layerSlots mu, foldl_sum fun l => layerSlots (5 + l), e1, e2]
  show 7 + 6 * (32 - 2) + 5 * ([h.v].length - 1) +
      ([h.v].map fun v => ((List.range v).map fun k => 2 * k + 5).sum).sum +
      ((List.range h.d).map fun l => 2 * (5 + l) + 5).sum + (1 + 5 + 2 * h.d) +
      (1 + 2 * (5 + h.d) + 2 + 1) =
    (1 + 0 * 2 + 3 + 3) + 30 * (1 + 0 * 2 + 3 + 2) + ((List.range h.v).map fun k => 2 * k + 5).sum +
      ((List.range h.d).map fun l => 2 * (5 + l) + 5).sum + (1 + 2 * h.d + 5) +
      (1 + (5 + h.d) * 2 + 2 + 1)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil]
  omega

#print axioms ProofFile.Honest.K3.Law.Spec.foldl_sum
#print axioms ProofFile.Honest.K3.Law.Spec.layerSlots_eq
#print axioms ProofFile.Honest.K3.Law.Spec.slots_elems

end ProofFile.Honest.K3.Law.Spec
