-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PlanFitsTest.lean: THE SMALLNESS TEST: THE PREMISE `PlanFitsAll`
OF ITS THEOREM AT THE FOLD (Johnson/P1K8R/FrontAtSeat.lean) FROM A TEST WITH CODE. NO SOUNDNESS.

  `planFitsAll_of_test`: `planFitsAllB W = true → PlanFitsAll W`
    (Johnson/Desc/First/K8/PlanFitsAll.lean).
  `k8Front_of_test`: **`k8Front` with the test in the premise's place.**
Limits. The test is evaluated at no public parameters here.

-/
import Johnson.P1K8R.FrontAtSeat
import Johnson.Desc.First.K8.PlanFitsAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Ready
open ProofFile (Cl)

/-- The test pays the premise. -/
theorem planFitsAll_of_test {W : Verify.Public} (h : planFitsAllB W = true) : PlanFitsAll W := by
  unfold planFitsAllB at h
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨hG, hA⟩, hH⟩ := h
  exact ⟨fun g hp e => hG hp (Array.mem_of_getElem? e), fun g a e => hA a (Array.mem_of_getElem? e),
    hH⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The theorem at the fold, under the test.** -/
theorem k8Front_of_test (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hW : planFitsAllB Bs.G₀.W = true) {x : ℕ × ℕ} (hx : x ∈ places) {Str : Type}
    (a : (ProofFile.InstPub × S) × Str)
    (h : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * x.1 + x.2 + 2) a) : frontB a.1.2 = true :=
  k8Front hS hR O (planFitsAll_of_test hW) hx a h

end P1K8S

#print axioms P1K8S.planFitsAll_of_test
#print axioms P1K8S.k8Front_of_test
