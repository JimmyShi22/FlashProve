-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/K5PublicAt.lean: KIND K5: THE PUBLIC PREMISES OF k5Fill_at (Johnson/Desc/First/Att/Door/Law/K5FillAt.lean [not in this library])
-- AT AN ATTENTION LINK m = 2 g + 1 OF THE PUBLIC PARAMETERS W (the plan derived from the public files): FROM PlanIs W · "attention is covered" · W.A[g]? = some a · the two places that lookAt hands · "the table's list of links has an attention link at m". Seven facts; no premise on a verifier's state, a witness or a filling. Mathlib beneath (through the guard's theorems).
import Johnson.Desc.First.Att.K05PlanOfPublic
import Johnson.Desc.First.Att.GuardPlan
import Johnson.Desc.First.Att.Door.PubK5
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.First.FillK4

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (lookAt placeAt k3SortAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Att.P (PlanIs guard_theorems place_calls planIs_next0 odd_facts)

theorem notHead {W : Verify.Public} (h4 : W.p4 = true) (g : ℕ) : K3.isHead W (2 * g + 1) = false := by
  unfold K3.isHead
  have := (odd_facts (W := W) (g := g) h4).1
  simpa using this

theorem sort2 {W : Verify.Public} (h4 : W.p4 = true) (g : ℕ) : k3SortAt W (2 * g + 1) 2 = some false := by
  unfold k3SortAt K3.pieceAt
  rw [notHead h4 g]
  rfl

theorem sort7 {W : Verify.Public} (h4 : W.p4 = true) (g : ℕ) : k3SortAt W (2 * g + 1) 7 = some true := by
  unfold k3SortAt K3.pieceAt
  rw [notHead h4 g]
  rfl

theorem att_not_lay {links : List ModelPart} {m : ℕ} (h : links[m]? = some .attention) : isLay links m = false := by
  unfold isLay
  rw [h]
  rfl

theorem isAtt_of (d : K5Data) {m : ℕ} (h : d.links[m]? = some .attention) : d.isAtt m = true := by
  unfold K5Data.isAtt
  rw [h]
  rfl

/-- **The door's first slot at an attention link is the number of the calls' lookup's scalars.** -/
theorem first_at (d : K5Data) (hP : PlanIs d.W) (h4 : d.W.p4 = true) {g : ℕ} {a : Attention.Plan} (ha : d.W.A[g]? = some a)
    {x : Look.Place} (hx : lookAt d.W (2 * g + 1) false = some x) : d.first? (2 * g + 1) = some (Forest.elems a.fs) := by
  have e1 := (guard_theorems hP h4 ha hx (Params.settingOf d.W.P.frame)).1
  obtain ⟨c1, _, _, c4⟩ := place_calls h4 ha hx
  have hz := planIs_next0 hP ha
  unfold K5Data.first? placeAt
  rw [hx]
  show ((Look.P.ofPlace (Params.settingOf d.W.P.frame) false x).shape.map fun hC => x.F.next + Forest.elems hC) = _
  rw [e1, c1, hz, c4]
  simp

theorem placeAt_of {W : Verify.Public} {m : ℕ} {dg : Bool} {x : Look.Place} (hx : lookAt W m dg = some x) :
    placeAt W m dg = some (Look.P.ofPlace (Params.settingOf W.P.frame) dg x) := by
  unfold placeAt
  rw [hx]
  rfl

#print axioms sort2
#print axioms sort7
#print axioms att_not_lay
#print axioms isAtt_of
#print axioms first_at
#print axioms placeAt_of

end H2K5.Door
