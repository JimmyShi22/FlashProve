-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/KnowWideIdle.lean: this file passes from knowledge soundness of the interactive oracle proof to
soundness for languages: the extractor's output is dropped.

One definition, statements and proofs.

Why: `BatchProtocol.PropsK` has a witness map that reads the instance and the oracles.


For a predicate between the two languages, which says nothing on which witness is extracted,
a wide witness map (Hiop/KnowWide.lean) is as good as a narrow one: replace the relations by
the idle ones,
    (i, x, _) is in the relation if some w is a witness of (i, x),
and the witness map by a constant w0. The type of the idle witness is free (Wn): the scheme's syntax
may name another type of witnesses than the interface's relations and map do (Wi). The goal "the
verifier rejects, or the index does not decode, or some witness exists" is weaker than "... or the
extracted witness is valid".

Main names:
  `Spec.soundAtK_idle_of_T`, `Spec.soundK_idle_of_T`, `Spec.soundKG_idle_of_T`: `BatchProtocol.SoundAtKT` /
    `SoundKT` / `SoundKGT` for (Rno, any wide map) give `SoundAtK` / `SoundK` / `SoundKG` for the
    idle relation and the constant map: same lists, same bound, same numbers of test bits.
  `Spec.propsK_idle_of_T`, `Spec.propsNoAccK_idle_of_T`: so `BatchProtocol.PropsKT` gives `BatchProtocol.PropsK`, and
    `PropsNoAccKT` gives `PropsNoAccK`, for the two idle relations, same numbers.

Limits: what is lost: all knowledge. The statements that come out speak of languages only. An
extractor that outputs a witness needs a door for the wide map itself.

Terms: lean/GLOSSARY.md.
-/
import Hiop.KnowWide

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- the idle relation: some witness exists -/
def idleRel {I X Wi : Type} (Wn : Type) (R : I → X → Wi → Prop) : I → X → Wn → Prop := fun i x _ =>
  ∃ w, R i x w

namespace Spec

def soundAtK_idle_of_T : Prop :=
  ∀ (I X Wi Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wi → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtKT Rno wit εT εL εB → ∀ w0 : Wn, L.SoundAtK (idleRel Wn Rno) (fun _ _ => w0) εT εL εB

def soundK_idle_of_T : Prop :=
  ∀ (I X Wi Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wi → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (εs : ℝ≥0∞),
    L.SoundKT Rno wit εs → ∀ w0 : Wn, L.SoundK (idleRel Wn Rno) (fun _ _ => w0) εs

def soundKG_idle_of_T : Prop :=
  ∀ (I X Wi Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wi → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (gT : GBits L.offline.shape)
      (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.SoundKGT Rno wit gT gL gB c → ∀ w0 : Wn, L.SoundKG (idleRel Wn Rno) (fun _ _ => w0) gT gL gB c

/-- All properties of `BatchProtocol.PropsK`, for the two idle relations. -/
def propsK_idle_of_T : Prop :=
  ∀ (I X Wi Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wi → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (M : LH.Nums),
    L.PropsKT Ryes Rno wit M →
    ∀ w0 : Wn, L.PropsK (idleRel Wn Ryes) (idleRel Wn Rno) (fun _ _ => w0) M

def propsNoAccK_idle_of_T : Prop :=
  ∀ (I X Wi Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wi → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (M : LH.Nums),
    L.PropsNoAccKT Ryes Rno wit M →
    ∀ w0 : Wn, L.PropsNoAccK (idleRel Wn Ryes) (idleRel Wn Rno) (fun _ _ => w0) M

end Spec

/-- for an element w0 of Wn: the language of the idle relation is the language of the relation -/
theorem idleRel_lang {I X Wi Wn : Type} (R : I → X → Wi → Prop) (w0 : Wn) :
    (fun i x => ∃ w, idleRel Wn R i x w) = fun i x => ∃ w, R i x w :=
  funext fun _ => funext fun _ => propext ⟨fun ⟨_, h⟩ => h, fun h => ⟨w0, h⟩⟩

theorem soundAtK_idle_of_T : Spec.soundAtK_idle_of_T := by
  intro I X Wi Wn L Rno wit εT εL εB h w0
  refine (soundAtK_iff_T I X Wn L (idleRel Wn Rno) (fun _ _ => w0) εT εL εB).2
    ⟨h.sndT, h.sndL, sndBKT_conseq X Wi Wn _ L.onlineBatch L.maxBatchSize L.early L.late _ _ wit _ εB ?_ h.sndB⟩
  rintro x y τ _ (hw | ⟨i, hi, hw⟩)
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, _, hw⟩

theorem soundK_idle_of_T : Spec.soundK_idle_of_T := by
  intro I X Wi Wn L Rno wit εs h w0
  obtain ⟨εT, εL, εB, hA, bT, bL, bB⟩ := (soundKT_iff_at I X Wi L Rno wit εs).1 h
  exact (soundAtK_idle_of_T I X Wi Wn L Rno wit εT εL εB hA w0).soundK bT bL bB

theorem soundKG_idle_of_T :
    Spec.soundKG_idle_of_T := fun I X Wi Wn L Rno wit _ _ _ _ ⟨εT, εL, εB, hA, b⟩ w0 =>
  ⟨εT, εL, εB, soundAtK_idle_of_T I X Wi Wn L Rno wit εT εL εB hA w0, b⟩

theorem propsK_idle_of_T : Spec.propsK_idle_of_T := by
  intro I X Wi Wn L Ryes Rno wit M h w0
  refine ⟨?_, soundK_idle_of_T I X Wi Wn L Rno wit M.εs h.soundKT w0⟩
  rw [idleRel_lang Ryes w0, idleRel_lang Rno w0]
  exact h.props

theorem propsNoAccK_idle_of_T : Spec.propsNoAccK_idle_of_T := by
  intro I X Wi Wn L Ryes Rno wit M h w0
  refine ⟨?_, soundK_idle_of_T I X Wi Wn L Rno wit M.εs h.soundKT w0⟩
  rw [idleRel_lang Ryes w0, idleRel_lang Rno w0]
  exact h.props

end Iop
