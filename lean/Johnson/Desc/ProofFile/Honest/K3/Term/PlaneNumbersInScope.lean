-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/PlaneNumbersInScope.lean: at public files in scope, the numbers
of the planes at the 25 segments are those that Sz.ref types by hand: the logarithm of a plane
matrix's rows (lmb, lmbA, lmbH), and the largest table kT and the number of calls NC of the segment's
lookup on the calls.

Main theorems: layerPlaneNumbers, attentionPlaneNumbers, headPlaneNumbers, one for each sort of
segment, in the form that OnBytes.HonestTrace's ties of places ask (Johnson/HonestTrace/PlacesTies.lean);
lookNumbersAtEverySegment: kT and NC by a segment's own name.

Not claimed: anything on cells; anything on soundness, completeness or zero knowledge.
-/
import Johnson.HonestTrace.PlaneLookNumbersInScope
import Johnson.HonestTrace.SzOfPublic
import Johnson.HonestTrace.FullPlanes
import Johnson.Goal.Meaning.LookScope
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Goal.Meaning.PlanNames
import Johnson.Desc.Kinds.Law.TablesPlanInScope
import Johnson.Desc.Kinds.Law.HeadFsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.HonestTrace (Sz Seg fsAt fsA lookNo)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Road (Hd.shapeA)

section
variable {Zl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- **At a layers' segment.** -/
theorem layerPlaneNumbers (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok X) (g : ℕ) :
    X.y.h.lmb = Sz.ref.lmb ∧ X.y.fo.kT = Sz.ref.kT (.ff g) ∧ X.y.fo.NC = Sz.ref.NC (.ff g) := by
  obtain ⟨-, -, ey, -⟩ := Meaning.scope_plans hZ hR h
  refine ⟨?_, OnBytes.HonestTrace.PlaneLook.layers_largest_table_in_scope hZ hR h, Meaning.P34.look_eight hZ hR h⟩
  rw [ey, Meaning.P34.shape_in_scope hZ hR h]
  rfl

/-- What a group's plan holds, by its number. -/
theorem attentionPlanIsAtItsNumber {g : ℕ} {a : OnBytes.Attention.Plan}
    (ha : X.A[g]? = some a) : Hd.shapeA X g = a.S ∧ fsAt X g = a.fs ∧ fsA X g = a.fs := by
  refine ⟨?_, ?_, ?_⟩
  · unfold OnBytes.Road.Hd.shapeA
    rw [ha]
    rfl
  · unfold fsAt
    rw [ha]
    rfl
  · unfold fsA
    rw [ha]
    rfl

/-- **At an attention segment.** -/
theorem attentionPlaneNumbers (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok X) {g : ℕ} (hg : g < 12) :
    (Hd.shapeA X g).cf.lmb = Sz.ref.lmbA ∧ (fsAt X g).kT = Sz.ref.kT (.att g) ∧
      (fsAt X g).NC = Sz.ref.NC (.att g) := by
  obtain ⟨-, a, ha, -⟩ := Meaning.scope_plans24 hZ hR h g hg
  obtain ⟨n1, k1⟩ := OnBytes.HonestTrace.PlaneLook.attention_lookup_numbers_in_scope hZ hR h ha
  obtain ⟨sc, midQ, lines, c, -, -, hf, -⟩ :=
    OnBytes.HonestTrace.PlaneLook.attention_configuration_is_the_fills h ha
  have e1 : a.S.cf.lmb = X.P.h.lmbA := OnBytes.HonestTrace.lmb_of_fill hf
  have e2 : X.P.h.lmbA = 14 := by
    rw [OnBytes.Road.Hd.scan_of_scope hZ hR h]
    rfl
  obtain ⟨es, ef, -⟩ := attentionPlanIsAtItsNumber ha
  rw [es, ef]
  exact ⟨e1.trans e2, k1, n1⟩

/-- **At the head's segment.** -/
theorem headPlaneNumbers (hZ : VerifierAndGoals.InScope Zl = true) (hR : VerifierAndGoals.readFiles Zl = .ok pp)
    (h : publicOf Zl.pol Zl.KL lay = .ok X) :
    X.hS.lmbH = Sz.ref.lmbH ∧ X.HLy.fs.kT = Sz.ref.kT .head ∧
      X.HLy.fs.NC = Sz.ref.NC .head := by
  obtain ⟨-, -, -, s4, -⟩ := VerifiableInference.Desc.Kinds.Head.Law.InScope.sizes_five hZ hR h
  have F := VerifiableInference.Desc.Kinds.Head.Law.InScope.fs_in_scope hZ hR h
  exact ⟨s4, F.kT, F.NC⟩

/-- **kT and NC at every segment of a proof with twelve groups.** -/
theorem lookNumbersAtEverySegment (hZ : VerifierAndGoals.InScope Zl = true)
    (hR : VerifierAndGoals.readFiles Zl = .ok pp) (h : publicOf Zl.pol Zl.KL lay = .ok X) (σ : Seg)
    (hσ : σ.Below 12) :
    lookNo (·.kT) X.y (fsA X) X.HLy σ = Sz.ref.kT σ ∧
      lookNo (·.NC) X.y (fsA X) X.HLy σ = Sz.ref.NC σ := by
  cases σ with
  | ff g =>
    obtain ⟨-, e1, e2⟩ := layerPlaneNumbers hZ hR h g
    exact ⟨e1, e2⟩
  | att g =>
    have hg : g < 12 := hσ
    obtain ⟨-, a, ha, -⟩ := Meaning.scope_plans24 hZ hR h g hg
    obtain ⟨-, e1, e2⟩ := attentionPlaneNumbers hZ hR h hg
    obtain ⟨-, ef, ea⟩ := attentionPlanIsAtItsNumber ha
    rw [ef, ← ea] at e1 e2
    exact ⟨e1, e2⟩
  | head =>
    obtain ⟨-, e1, e2⟩ := headPlaneNumbers hZ hR h
    exact ⟨e1, e2⟩

end

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.layerPlaneNumbers
#print axioms ProofFile.Honest.K3.Term.attentionPlanIsAtItsNumber
#print axioms ProofFile.Honest.K3.Term.attentionPlaneNumbers
#print axioms ProofFile.Honest.K3.Term.headPlaneNumbers
#print axioms ProofFile.Honest.K3.Term.lookNumbersAtEverySegment
