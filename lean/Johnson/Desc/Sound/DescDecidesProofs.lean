-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DescDecidesProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/DescDecides.lean.

Limits: those of Johnson/Desc/Sound/DescDecides.lean.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.DescDecides
import Johnson.Desc.Sound.DescThreeProofs
import Johnson.Desc.Sound.FileDecidesProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

theorem some_unit (o : Option Unit) (h : o.isSome = true) : o = some () := by
  cases o with
  | none => cases h
  | some u => rfl

theorem wholeMono : WholeMono := by
  intro C D Y TF TJ T3 tF tJ t3 silent silent' run run' x x' hs hr y τ h
  have h' : ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true := by
    rw [h]
    rfl
  obtain ⟨p, f, k, s, r⟩ := (wholeIOR_out_iff C D tF tJ t3 y τ silent run x).1 h'
  exact some_unit _ ((wholeIOR_out_iff C D tF tJ t3 y τ silent' run' x').2
    ⟨p, f, k, hs _ _ _ s, hr _ _ _ r⟩)

/-- The first run reads the instance through its public part alone. -/
theorem descRun₁_reads {Xi : Type} (F : FileDescription Xi) (x x' : Xi) (h : F.pub x' = F.pub x) :
    descRun₁ F x' = descRun₁ F x := by
  funext v
  unfold descRun₁
  rw [h]

theorem descDecides : DescDecides := by
  intro C D all Xi X₁ X₂ W TF TJ T3 tF tJ t3 F T okF okJ ok3 silent P hO hfit hF hJ h3 x x' y τ hp
    hs h
  obtain ⟨e₁, e₂, e₃⟩ := runsAtDesc C D all Xi X₁ X₂ W F T hO
  refine fileDecides C D all Xi _ _ _ _ _ F.Cl W TF TJ T3 tF tJ t3 (atDesc F T) okF okJ ok3 silent
    P hfit hF hJ h3 x' y τ ?_
  refine wholeMono C D Xi TF TJ T3 tF tJ t3 silent silent F.run _ x x' hs ?_ y τ h
  intro v₁ v₂ v₃ hy
  rw [e₁, e₂, e₃]
  have k := runGivesRow Xi F x v₁ v₂ v₃ hy
  unfold runRow at k ⊢
  rw [descRun₁_reads F x x' hp]
  exact k

theorem wholeGivesEnds : WholeGivesEnds := by
  intro C D Xi TF TJ T3 tF tJ t3 F silent x y τ h
  have h' : ((reductionOfWholeFile C D tF tJ t3 silent F.run).out x y τ).isSome = true := by
    rw [h]
    rfl
  have hy := wholeIOR_out_views C D tF tJ t3 y τ silent F.run x h'
  unfold FileDescription.run at hy
  cases hr : F.runEnd x (view₁ C D tF tJ t3 y τ) (view₂ C D tF tJ t3 y τ)
      (view₃ C D tF tJ t3 y τ) with
  | error m =>
    rw [hr] at hy
    cases hy
  | ok t =>
    obtain ⟨e₁, e₂, e₃⟩ := t
    exact ⟨e₁, e₂, e₃, (runEndIs Xi F x _ _ _ e₁ e₂ e₃).1 hr⟩

end VerifiableInference.Desc.Sound
