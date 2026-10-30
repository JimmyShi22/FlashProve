-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/EqSizesInScope.lean: THE CLOSED TEST eqSizesYes (K9/EqValuesJ.lean) AT EVERY FILE IN SCOPE, FROM THE ANSWER AT THE
STORED FILES: where the run on shapes over the second text at the stored files returns at border b and oneShape accepts there, the run over
the table's own steps under the head at Z returns at b and oneShape accepts there. oneShape_blind: the test cannot part what RelAt relates.

Limits. hT is a premise: a closed line at the stored files. 14 l + 11 and 349 are no cuts of the pieces: hT is paid by a tested run from member 0, in the form of
eqSizesYes_of_tested. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.YesAll
import Johnson.Desc.ProofFile.Honest.K9.EqBlind
import Johnson.Desc.ProofFile.Honest.K9.EqValuesJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest.K9 (oneShape eqSizesYes oneShape_blind)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- oneShape cannot part what RelAt relates. -/
theorem oneShape_rel {X X₀ : Verify.Public} {b : Nat} {a a' : ShA} (h : RelAt X X₀ b a a') :
    oneShape a.1 = oneShape a'.1 := by
  unfold RelAt at h
  split at h
  · exact oneShape_blind h
  · rw [h]

/-- **The closed test at every file in scope, from the stored files.** -/
theorem eqSizesYes_in_scope (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {b : Nat} (hb : b ≤ 358)
    (hT : ∃ c : ShA, (shapeL (LWn X₀)).run b startShA = .ok c ∧ oneShape c.1 = true) :
    eqSizesYes (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀) startShA b = true := by
  obtain ⟨c, hc, h1⟩ := hT
  obtain ⟨c', e, y⟩ := bool_at_scope h hB hX₀ hb (fun a => oneShape a.1)
    (fun _ _ hr => oneShape_rel hr) hc h1
  unfold eqSizesYes
  rw [e]
  exact y

/-- The same from a tested run from member 0. -/
theorem eqSizesYes_of_tested (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    {b : Nat} (hb : b ≤ 358)
    (hT : ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 b startShA = .ok c ∧ oneShape c.1 = true) :
    eqSizesYes (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀) startShA b = true := by
  obtain ⟨c, hc, h1⟩ := hT
  refine eqSizesYes_in_scope h hB hX₀ hb ⟨c, ?_, h1⟩
  have k := ProofFile.Honest.run_add (shapeL (LWn X₀)) 0 b startShA
  rw [Nat.zero_add] at k
  rw [k]
  exact hc

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.eqSizesYes_of_tested
#print axioms Johnson.AtFull.Shape.Scope.oneShape_rel
#print axioms Johnson.AtFull.Shape.Scope.eqSizesYes_in_scope
