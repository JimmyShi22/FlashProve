-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ShapeAtAll.lean: THE TEST `shapeHB` (Johnson/Desc/K1/Law/PlanesAtAll.lean: the
shape of the lookup on the calls at segment 24 has the view of the output head's layout's own
shape) ACCEPTS AT ALL PUBLIC FILES IN THE GOALS' SCOPE: a theorem: nothing is evaluated. Statements
with their proofs.

  `hShape_in_scope`   the sentence hShape of `planesLeft4_at342` (ArmPlanesHostAt.lean, this
      folder): by `shape_at` (Johnson/Desc/First/Look/K3CallerPlanesAt.lean: at
      every return of the reader of the public files the lookup's own parameters make the place's
      shape) and the text of `lookAt` (Johnson/Desc/First/Look/LookAt.lean), which at the head's
      segment lays the head's layout's shape; in scope the head's segment is number 24
      (`Meaning.scope_plans`)
  `shapeH_in_scope`   so the test accepts
  `shapeH_atAll`   **the test accepts at the closed constant's public parameters**,
      under the head alone

What is not claimed. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.PlanesAtAll
import Johnson.Desc.First.Look.K3CallerPlanesAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (sameForestV_iff)
open ProofFile (Cl)

/-- **hShape, in scope.** -/
theorem hShape_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : Verify.publicOf Z.pol Z.KL lay = .ok X) :
    ∀ p h, First.Look.placeAt X 24 false = some p → p.shape = some h → h = X.HLy.fs := by
  intro p h hp hs
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans hS hR hX
  unfold First.Look.placeAt at hp
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hp
  have e : h = x.fs := Option.some.inj (hs.symm.trans (First.Look.shape_at _ hX hx))
  rw [e]
  simp [First.Look.lookAt, p4, ng] at hx
  rw [← hx]

/-- So the test accepts. -/
theorem shapeH_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Verify.Public} (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : Verify.publicOf Z.pol Z.KL lay = .ok X) : shapeHB X = true := by
  unfold shapeHB
  cases hp : First.Look.placeAt X 24 false with
  | none => rfl
  | some p =>
    cases hs : p.shape with
    | none =>
      rw [Option.bind_some, hs]
      rfl
    | some h =>
      rw [Option.bind_some, hs, Option.all_some, hShape_in_scope hS hR hX p h hp hs]
      exact (sameForestV_iff _ _).2 rfl

/-- **The test accepts at the constant's public parameters.** -/
theorem shapeH_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) : shapeHB (P5J.At.X Zp) = true :=
  shapeH_in_scope hA.scope hA.reads hA.pubOne

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hShape_in_scope
#print axioms VerifiableInference.Desc.K1.shapeH_in_scope
#print axioms VerifiableInference.Desc.K1.shapeH_atAll
