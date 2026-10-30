-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/BearsProofs.lean: proofs of the statements of Ior/Bears.lean.

The implicit instance: the implicit part of a statement.

Main names (statements and hypotheses: Ior/Bears.lean):
  `need_seq`: the needed positions of a composition.

The equations behind `need_seq`: what the simulator of a composition is given at the further
positions T is what the first simulator is given at `firstT` (Ior/ExactSeq.lean) together with the
sources, in the old implicit instance, of what the second simulator is given (`given_seq`); and at T
= the sources of U the set `firstT` is the set of the sources of what the second needs
(`firstT_src`).

Stated and proved here: `Cb.bears_post`: a step without rounds after an IOR: a set U of positions of
the new implicit instance is taken back along the step's map (under the hypotheses of its
statement).

Limits: see Limits in the head of Ior/Bears.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Bears
import Ior.FrameProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {X₁ X₂ X₃ Xi Xi' Xo : Type} {E₁ E₂ E₃ Ei Ei' Eo : ExtSpec}

open Classical in
theorem mem_need {R : IOR Xi Ei Xo Eo} {ρ : Rho R.shape} {U : Finset Eo.Pos} {q : Ei.Pos} :
    q ∈ R.need ρ U ↔ q ∈ R.given ρ (U.biUnion (R.srcO ρ)) ∨ ∃ u ∈ U, q ∈ R.srcE ρ u := by
  unfold need
  rw [Finset.mem_union, Finset.mem_biUnion]

section Seq
variable (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)

open Classical in
/-- What the simulator of a composition is given. -/
theorem given_seq (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape))) :
    (R₁.seq R₂).given ρ T =
      R₁.given (Rho.fst ρ) (firstT R₁ R₂ ρ T) ∪
        (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)).biUnion
          (R₁.srcE (Rho.fst ρ)) := by
  refine Finset.Subset.antisymm ?_ (Finset.union_subset (given_first_subset ρ T) fun q hq => ?_)
  · intro q hq
    rw [Finset.mem_union, Finset.mem_biUnion]
    rcases mem_given.1 hq with hq | ⟨p, hp, hq⟩
    · rcases (mem_seq_extReads R₁ R₂ _ _).1 hq with hq | ⟨e, he, hq⟩
      · exact Or.inl (mem_given.2 (Or.inl hq))
      · exact Or.inr ⟨e, mem_given.2 (Or.inl he), hq⟩
    · rcases left_or_right p with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · rw [seq_tie_left] at hq
        refine Or.inl (mem_given.2 (Or.inr ⟨r, ?_, hq⟩))
        rcases hp with hp | hp
        · rcases (left_mem_seq_reads R₁ R₂ _ _).1 hp with hp | ⟨e, he, hp⟩
          · exact Or.inl hp
          · exact Or.inr (mem_firstT.2 (Or.inr ⟨e, mem_given.2 (Or.inl he), hp⟩))
        · exact Or.inr (mem_firstT.2 (Or.inl hp))
      · have hr : r ∈ R₂.reads (Rho.snd (s := R₁.shape) ρ) ∨ r ∈ partR R₁.shape T :=
          hp.imp (right_mem_seq_reads R₁ R₂ _ _).1 mem_partR.2
        obtain ⟨e, he, hq⟩ := (mem_seq_tie_right R₁ R₂ _ _ _).1 hq
        have he' : e ∈ R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T) :=
          mem_given.2 (Or.inr ⟨r, hr, he⟩)
        rcases hq with hq | ⟨p₁, hp₁, hq⟩
        · exact Or.inr ⟨e, he', hq⟩
        · exact Or.inl (mem_given.2 (Or.inr ⟨p₁, Or.inr (mem_firstT.2 (Or.inr ⟨e, he', hp₁⟩)), hq⟩))
  · obtain ⟨e, he, hq⟩ := Finset.mem_biUnion.1 hq
    exact srcE_subset_given he hq

open Classical in
theorem partR_src (ρ : Rho (R₁.shape ++ R₂.shape)) (U : Finset E₃.Pos) :
    partR R₁.shape (U.biUnion ((R₁.seq R₂).srcO ρ)) =
      U.biUnion (R₂.srcO (Rho.snd (s := R₁.shape) ρ)) := by
  ext p
  rw [mem_partR, Finset.mem_biUnion, Finset.mem_biUnion]
  exact exists_congr fun u => and_congr_right fun _ => right_mem_seq_srcO R₁ R₂ ρ u p

open Classical in
/-- At the sources of U, the further positions for the first simulator are the sources of what the
second needs. -/
theorem firstT_src (ρ : Rho (R₁.shape ++ R₂.shape)) (U : Finset E₃.Pos) :
    firstT R₁ R₂ ρ (U.biUnion ((R₁.seq R₂).srcO ρ)) =
      (R₂.need (Rho.snd (s := R₁.shape) ρ) U).biUnion (R₁.srcO (Rho.fst ρ)) := by
  ext p
  rw [mem_firstT, partR_src, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro (⟨u, hu, hp⟩ | ⟨e, he, hp⟩)
    · obtain ⟨e, he, hp⟩ := (left_mem_seq_srcO R₁ R₂ ρ u p).1 hp
      exact ⟨e, mem_need.2 (Or.inr ⟨u, hu, he⟩), hp⟩
    · exact ⟨e, mem_need.2 (Or.inl he), hp⟩
  · rintro ⟨e, he, hp⟩
    rcases mem_need.1 he with he | ⟨u, hu, he⟩
    · exact Or.inr ⟨e, he, hp⟩
    · exact Or.inl ⟨u, hu, (left_mem_seq_srcO R₁ R₂ ρ u p).2 ⟨e, he, hp⟩⟩

end Seq
end IOR

open IOR

theorem need_seq : Spec.need_seq := by
  classical
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ ρ U
  have hg : (R₁.seq R₂).given ρ (U.biUnion ((R₁.seq R₂).srcO ρ)) =
      R₁.given (Rho.fst ρ) ((R₂.need (Rho.snd (s := R₁.shape) ρ) U).biUnion (R₁.srcO (Rho.fst ρ))) ∪
        (R₂.given (Rho.snd (s := R₁.shape) ρ)
            (U.biUnion (R₂.srcO (Rho.snd (s := R₁.shape) ρ)))).biUnion
          (R₁.srcE (Rho.fst ρ)) := by
    have h := given_seq R₁ R₂ ρ (U.biUnion ((R₁.seq R₂).srcO ρ))
    rw [firstT_src, partR_src] at h
    exact h
  ext q
  rw [mem_need, hg, Finset.mem_union, Finset.mem_biUnion, mem_need]
  constructor
  · rintro ((h | ⟨e, he, hq⟩) | ⟨u, hu, hq⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, mem_need.2 (Or.inl he), hq⟩
    · obtain ⟨e, he, hq⟩ := (mem_seq_srcE R₁ R₂ ρ u q).1 hq
      exact Or.inr ⟨e, mem_need.2 (Or.inr ⟨u, hu, he⟩), hq⟩
  · rintro (h | ⟨e, he, hq⟩)
    · exact Or.inl (Or.inl h)
    · rcases mem_need.1 he with he | ⟨u, hu, he⟩
      · exact Or.inl (Or.inr ⟨e, he, hq⟩)
      · exact Or.inr ⟨u, hu, (mem_seq_srcE R₁ R₂ ρ u q).2 ⟨e, he, hq⟩⟩

theorem bears_seq : Spec.bears_seq := by
  classical
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ b₁ b₂ qa qb qc h₁ h₂ ρ U hU
  obtain ⟨hb₂, hq₂⟩ := h₂ (Rho.snd (s := R₁.shape) ρ) U hU
  obtain ⟨hb₁, hq₁⟩ := h₁ (Rho.fst ρ) _ hq₂
  refine ⟨?_, by rw [need_seq]; exact hq₁⟩
  intro T₁ T₂ hT₁ hT₂
  have e₂ : T₂ = partR R₁.shape (U.biUnion ((R₁.seq R₂).srcO ρ)) :=
    Finset.ext fun p => (hT₂ p).trans mem_partR.symm
  have e₁ : T₁ = partL (U.biUnion ((R₁.seq R₂).srcO ρ)) :=
    Finset.ext fun p => (hT₁ p).trans mem_partL.symm
  subst e₁ e₂
  have e := firstT_src R₁ R₂ ρ U
  unfold firstT at e
  rw [e, partR_src]
  exact ⟨hb₂, hb₁⟩

theorem bears_mono : Spec.bears_mono := fun _ _ _ _ _ _ _ _ _ _ _ h hb hi ho ρ U hU =>
  ⟨hb _ _ (h ρ U (ho U hU)).1, hi _ (h ρ U (ho U hU)).2⟩

theorem bears_pre : Spec.bears_pre := by
  classical
  intro Xi Xi' Xo Ei Ei' Eo R f g bud qi qi' qo h hq ρ U hU
  obtain ⟨hb, hn⟩ := h ρ U hU
  refine ⟨hb, ?_⟩
  have e : (R.pre f g).need ρ U = (R.need ρ U).biUnion g.src := by
    ext p
    rw [mem_need, Finset.mem_biUnion]
    constructor
    · rintro (hp | ⟨u, hu, hp⟩)
      · rcases mem_given.1 hp with hp | ⟨r, hr, hp⟩
        · obtain ⟨q, hq', hp⟩ := Finset.mem_biUnion.1 hp
          exact ⟨q, mem_need.2 (Or.inl (mem_given.2 (Or.inl hq'))), hp⟩
        · obtain ⟨q, hq', hp⟩ := Finset.mem_biUnion.1 hp
          exact ⟨q, mem_need.2 (Or.inl (mem_given.2 (Or.inr ⟨r, hr, hq'⟩))), hp⟩
      · obtain ⟨q, hq', hp⟩ := Finset.mem_biUnion.1 hp
        exact ⟨q, mem_need.2 (Or.inr ⟨u, hu, hq'⟩), hp⟩
    · rintro ⟨q, hq', hp⟩
      rcases mem_need.1 hq' with hq' | ⟨u, hu, hq'⟩
      · exact Or.inl (src_subset_given_pre f g hq' hp)
      · exact Or.inr ⟨u, hu, Finset.mem_biUnion.2 ⟨q, hq', hp⟩⟩
  rw [e]
  exact hq _ hn

theorem bears_end : Spec.bears_end := by
  classical
  intro Xi Xo Ei Eo R bud qi qo h h0 ρ
  have := h ρ ∅ h0
  unfold need at this
  simpa using this

theorem noHid_seq : Spec.noHid_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ h₁ h₂ w x
  refine Set.eq_empty_of_forall_notMem fun ρ hρ => ?_
  rcases hρ with hρ | ⟨_, c, hc⟩
  · have : Rho.fst (s := R₁.shape) (t := R₂.shape) ρ ∈ H₁.Hid w x := hρ
    rw [h₁] at this
    exact this
  · rw [h₂] at hc
    exact hc

theorem noTie_seq : Spec.noTie_seq := by
  classical
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ h₁ h₂ ρ p
  rcases left_or_right (s := R₁.shape) (t := R₂.shape) p with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [seq_tie_left]
    exact h₁ _ _
  · refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
    obtain ⟨e, he, _⟩ := (mem_seq_tie_right R₁ R₂ _ _ _).1 hq
    rw [h₂] at he
    exact absurd he (Finset.notMem_empty _)

theorem noTie_pre : Spec.noTie_pre := by
  classical
  intro Xi Xi' Xo Ei Ei' Eo R f g h ρ p
  show (R.tie ρ p).biUnion g.src = ∅
  rw [h]
  rfl

theorem tied_seq : Spec.tied_seq := by
  classical
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ h₁ h₂ ρ p hp q hq
  rcases left_or_right (s := R₁.shape) (t := R₂.shape) p with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [seq_tie_left, h₁] at hq
    exact absurd hq (Finset.notMem_empty _)
  · obtain ⟨e, he, hq⟩ := (mem_seq_tie_right R₁ R₂ _ _ _).1 hq
    rcases hq with hq | ⟨p₁, _, hq⟩
    · exact (mem_seq_extReads R₁ R₂ _ _).2
        (Or.inr ⟨e, h₂ _ r ((right_mem_seq_reads R₁ R₂ _ _).1 hp) he, hq⟩)
    · rw [h₁] at hq
      exact absurd hq (Finset.notMem_empty _)

theorem tied_pre : Spec.tied_pre := by
  classical
  intro Xi Xi' Xo Ei Ei' Eo R f g h ρ p hp q hq
  obtain ⟨e, he, hq⟩ := Finset.mem_biUnion.1 (show q ∈ (R.tie ρ p).biUnion g.src from hq)
  exact Finset.mem_biUnion.2 ⟨e, h ρ p hp he, hq⟩

end Iop

namespace Cb
open Iop Prob IOR

section
variable {Xi Xo Xo' : Type} {Ei Eo Eo' : ExtSpec}

/-- A step without rounds after R. V stands for the set of the sources, under the step's map, of the
positions in U. -/
theorem bears_post (R : IOR Xi Ei Xo Eo) (f : Xo → Option Xo') (g : ExtMap Eo Eo')
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (qi : Finset Ei.Pos → Prop)
    (qo : Finset Eo.Pos → Prop) (qo' : Finset Eo'.Pos → Prop) (h : R.Bears bud qi qo)
    (hq : ∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ g.src u) → qo' U → qo V) :
    (R.post f g).Bears bud qi qo' := by
  classical
  intro ρ U hU
  have h0 := h ρ (U.biUnion g.src) (hq U _ (fun x => Finset.mem_biUnion) hU)
  have e1 : U.biUnion ((R.post f g).srcO ρ) = (U.biUnion g.src).biUnion (R.srcO ρ) := by
    ext p
    constructor
    · intro hp
      obtain ⟨u, hu, hp⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨e, he, hp'⟩ := Finset.mem_biUnion.1 hp
      exact Finset.mem_biUnion.2 ⟨e, Finset.mem_biUnion.2 ⟨u, hu, he⟩, hp'⟩
    · intro hp
      obtain ⟨e, he, hp⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨u, hu, he⟩ := Finset.mem_biUnion.1 he
      exact Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_biUnion.2 ⟨e, he, hp⟩⟩
  have e2 : U.biUnion ((R.post f g).srcE ρ) = (U.biUnion g.src).biUnion (R.srcE ρ) := by
    ext p
    constructor
    · intro hp
      obtain ⟨u, hu, hp⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨e, he, hp'⟩ := Finset.mem_biUnion.1 hp
      exact Finset.mem_biUnion.2 ⟨e, Finset.mem_biUnion.2 ⟨u, hu, he⟩, hp'⟩
    · intro hp
      obtain ⟨e, he, hp⟩ := Finset.mem_biUnion.1 hp
      obtain ⟨u, hu, he⟩ := Finset.mem_biUnion.1 he
      exact Finset.mem_biUnion.2 ⟨u, hu, Finset.mem_biUnion.2 ⟨e, he, hp⟩⟩
  have e3 : (R.post f g).need ρ U = R.need ρ (U.biUnion g.src) := by
    unfold IOR.need
    rw [e1, e2]
    rfl
  exact ⟨by rw [e1]; exact h0.1, by rw [e3]; exact h0.2⟩

end

end Cb
