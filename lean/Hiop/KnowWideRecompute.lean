-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/KnowWideRecompute.lean: this file is about knowledge soundness of the interactive oracle proof:
an extractor that reads the instance and the encoded index, and nothing of the transcript.

Definitions, statements and proofs, for any `BatchProtocol` (Iop/Batch.lean) with a
wide witness map (Hiop/KnowWide.lean) and for the object with records (`HolographicProtocol`,
Hiop/RecInterface.lean). A witness map is the extractor named in round-by-round knowledge soundness
for the instances of a batch (`SndBKT`, Ior/KnowWide.lean). A wide witness map may read the
instance, the encoded index and the whole local transcript.

Let `tr i x` be a function of index and instance such that, whenever x has some witness in Rno for
i, `tr i x` is one. (For a configuration with `ConfigurationWithOutOfDomainSample.Props` (`admits`, `sub`): the cells that the
honest prover computes, as soon as every instance with a witness in Rno has one in Ryes:
CompileK/Recompute.lean says so for the compiled argument.)

Main names:
  `L.witRe tr w0`: the witness map fun x y _ => tr (the index to which y decodes) x; w0 where y does
    not decode. It reads the instance and the encoded index; nothing of the transcript: no oracle of
    the prover, no plain part, no verifier message.
  `Spec.soundAtKT_recompute`, `Spec.soundKT_recompute`, `Spec.soundKGT_recompute`,
    `Spec.propsKT_recompute`: for such a tr, any witness map may be replaced by it: same lists, same
    bound, same numbers.
  `Spec.soundAtR_recompute`, `Spec.soundR_recompute`, `Spec.propsR_recompute`: the same for the
    object with records, at `L.witReR`.
  `Spec.sndBKT_of_sndB`: and no witness map is needed to begin with, when the whole instance stands
    in the first query (early = id, late = none): (Snd-B) for a language gives (Snd-B) with a
    witness for every relation R and every map d of (instance, external oracle) such that d x y is a
    witness wherever (x, y) is in the language. Same errors. (The wide form of `sndBK_of_sndB`,
    Ior/Batch.lean, whose d reads the instance alone.)
  `Spec.witRe_blind`: by parts, `L.witRe tr w0` reads no verifier message (`WitP.BlindFrom 0`,
    Ior/KnowWidePass.lean).

Limits: with this map the witness clause says no more than soundness for the language of Rno at the
decoded index (as CompileK/Recompute.lean says of the compiled argument): it is free (in Lean at
early = id, late = none: `Spec.sndBKT_of_sndB`; at other `early`, `late` this file does not say that
the clause says more). It is what an extractor of a compiled argument can compute from the key, the
committer's trace and the instance alone.
What the other witness maps add (backward extractors: `S.wit`, Hiop/RecBuild.lean; the decoder of
the oracles of cells: Hiop/RecDecode.lean) is of another kind: that a valid witness stands in what
the prover sent. (That holds for a map that reads only what the prover sent, in the sense of
`Spec.rec_soundAt` (Hiop/RecMain.lean) and `Spec.rec_soundAt_dec` (Hiop/RecDecode.lean), each under
the hypotheses of its statement.) These statements stay true and are the stronger ones at the level
of the IOP.
`S.wit` (Hiop/RecBuild.lean) runs the field `S.cellsOf` (Hiop/RecSubs.lean), and `S.witDec dC`
(Hiop/RecDecode.lean) runs its argument `dC`; by type `S.cellsOf` and `dC` may also read the slot's
statement (instance, record, encoded index) and the verifier's messages of the preamble.
This file says nothing on running times: tr may be a forward pass or a search.

Terms: lean/GLOSSARY.md: object, record, wide, witness map, encoded index, local transcript,
  (Snd-B), configuration, cells, plain part, slot, preamble.
-/
import Hiop.RecDecode

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

variable {I X Wn : Type}

/-- The witness map that recomputes. -/
def BatchProtocol.witRe (L : BatchProtocol I X) (tr : I → X → Wn) (w0 : Wn) :
    X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn :=
  fun x y _ => ((L.decodeIndex y).map fun i => tr i x).getD w0

/-- the same with a record -/
def HolographicProtocol.witReR (L : HolographicProtocol I X) (tr : I → X → Wn) (w0 : Wn) :
    X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn :=
  fun a y _ => ((L.decodeIndex y a.2).map fun i => tr i a.1).getD w0

namespace Spec

def soundAtKT_recompute : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (tr : I → X → Wn) (w0 : Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) →
    L.SoundAtKT Rno wit εT εL εB → L.SoundAtKT Rno (L.witRe tr w0) εT εL εB

def soundKT_recompute : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (tr : I → X → Wn) (w0 : Wn) (εs : ℝ≥0∞),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) →
    L.SoundKT Rno wit εs → L.SoundKT Rno (L.witRe tr w0) εs

def soundKGT_recompute : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (tr : I → X → Wn) (w0 : Wn)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) → L.SoundKGT Rno wit gT gL gB c →
    L.SoundKGT Rno (L.witRe tr w0) gT gL gB c

def propsKT_recompute : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (tr : I → X → Wn)
      (w0 : Wn) (M : LH.Nums),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) →
    L.PropsKT Ryes Rno wit M → L.PropsKT Ryes Rno (L.witRe tr w0) M

def soundAtR_recompute : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (tr : I → X → Wn) (w0 : Wn)
      (eR : ℕ) (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) → L.SoundAtR Rno wit eR εT εL εB →
    L.SoundAtR Rno (L.witReR tr w0) eR εT εL εB

def soundR_recompute : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
      (tr : I → X → Wn) (w0 : Wn) (εs : ℝ≥0∞),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) → L.SoundR Rno wit εs → L.SoundR Rno (L.witReR tr w0) εs

def propsR_recompute : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (tr : I → X → Wn)
      (w0 : Wn) (M : LH.Nums),
    (∀ i x w, Rno i x w → Rno i x (tr i x)) →
    L.PropsR Ryes Rno wit M → L.PropsR Ryes Rno (L.witReR tr w0) M

/-- States: (Snd-B) for a language gives (Snd-B) with a witness, when instance and external oracle
determine a witness. -/
def sndBKT_of_sndB : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (N : ℕ) (L : X → E.Str → Prop)
      (R : X → E.Str → W → Prop) (d : X → E.Str → W) (ε : Err Q.loc.shape),
    Q.SndB N L ε → (∀ x y, L x y → R x y (d x y)) → Q.SndBKT N id none R (fun x y _ => d x y) ε

/-- States: by parts, the map that recomputes reads no verifier message -/
def witRe_blind : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (tr : I → X → Wn) (w0 : Wn),
    L.witRe tr w0 = witOf (fun x y _ _ _ => ((L.decodeIndex y).map fun i => tr i x).getD w0) ∧
    WitP.BlindFrom 0 (fun x (y : (oneExternalString L.wordLength L.Symbol).Str) (_ : Orcs L.onlineBatch.loc.shape)
      (_ : Plains L.onlineBatch.loc.shape) (_ : Rho L.onlineBatch.loc.shape) =>
        ((L.decodeIndex y).map fun i => tr i x).getD w0)

end Spec

theorem soundAtKT_recompute :
    Spec.soundAtKT_recompute := fun I X Wn L Rno wit tr w0 εT εL εB htr h =>
  soundAtKT_conseq I X Wn L Rno wit (L.witRe tr w0) εT εL εB (fun i x y τ hi _ hw => by
    show Rno i x (((L.decodeIndex y).map fun i => tr i x).getD w0)
    rw [hi]
    exact htr i x _ hw) h

theorem soundKT_recompute : Spec.soundKT_recompute := by
  intro I X Wn L Rno wit tr w0 εs htr h
  obtain ⟨εT, εL, εB, hA, b⟩ := (soundKT_iff_at I X Wn L Rno wit εs).1 h
  exact (soundKT_iff_at I X Wn L Rno _ εs).2
    ⟨εT, εL, εB, soundAtKT_recompute I X Wn L Rno wit tr w0 εT εL εB htr hA, b⟩

theorem soundKGT_recompute :
    Spec.soundKGT_recompute := fun I X Wn L Rno wit tr w0 _ _ _ _ htr ⟨εT, εL, εB, hA, b⟩ =>
  ⟨εT, εL, εB, soundAtKT_recompute I X Wn L Rno wit tr w0 εT εL εB htr hA, b⟩

theorem propsKT_recompute : Spec.propsKT_recompute := fun I X Wn L _ Rno wit tr w0 M htr h =>
  ⟨h.props, soundKT_recompute I X Wn L Rno wit tr w0 M.εs htr h.soundKT⟩

/-- the step for the object with records -/
theorem HolographicProtocol.witReR_valid {L : HolographicProtocol I X} {Rno : I → X → Wn → Prop}
    {wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn} {tr : I → X → Wn} (w0 : Wn)
    (htr : ∀ i x w, Rno i x w → Rno i x (tr i x)) :
    ∀ rec i x y τ, L.decodeIndex y rec = some i → L.onlineBatch.loc.accept (x, rec) y τ = true →
      Rno i x (wit (x, rec) y τ) → Rno i x (L.witReR tr w0 (x, rec) y τ) := by
  intro rec i x y τ hi _ hw
  show Rno i x (((L.decodeIndex y rec).map fun i => tr i x).getD w0)
  rw [hi]
  exact htr i x _ hw

theorem soundAtR_recompute :
    Spec.soundAtR_recompute := fun I X Wn L Rno wit tr w0 eR εT εL εB htr h =>
  soundAtR_conseq I X Wn L Rno wit (L.witReR tr w0) eR εT εL εB (HolographicProtocol.witReR_valid w0 htr) h

theorem soundR_recompute : Spec.soundR_recompute := fun I X Wn L Rno wit tr w0 εs htr h =>
  soundR_conseq I X Wn L Rno wit (L.witReR tr w0) εs (HolographicProtocol.witReR_valid w0 htr) h

theorem propsR_recompute : Spec.propsR_recompute := fun I X Wn L Ryes Rno wit tr w0 M htr h =>
  propsR_conseq I X Wn L Ryes Rno wit (L.witReR tr w0) M (HolographicProtocol.witReR_valid w0 htr) h

theorem sndBKT_of_sndB : Spec.sndBKT_of_sndB := by
  classical
  intro X W E Q N L R d ε
  rintro ⟨State, h1, h2, h3, h4⟩ hLR
  refine (sndBP_iff X E Q N _ ε).2 ⟨fun y x τ => !decide (L x y) && State y x τ, fun y x => ?_,
    fun y x τ m h => ?_, fun y x τ h ha => ?_, fun y x => ?_⟩
  · by_cases hL : L x y
    · simp [hL]
    · have : State y x (PTr.empty Q.loc.shape) = false :=
        Bool.eq_false_iff.2 fun h => hL ((h1 y x).1 h)
      simp [this]
  · by_cases hL : L x y
    · simp [hL]
    · have h' : State y x (.atP τ) = false := by simpa [hL] using h
      simp [h2 y x τ m h']
  · by_cases hL : L x y
    · exact hLR x y hL
    · have h' : State y x (.full τ) = false := by simpa [hL] using h
      rw [h3 y x τ h'] at ha
      cases ha
  · have h5 := BatchK.jointLaw_andFlag
      _ _ ε _ (fun j => ((x j).map fun xj => !decide (L xj y)).getD false) (h4 y x)
    refine cast (congrArg (JointLaw N Q.loc.shape Q.ann ε) ?_) h5
    funext j
    beta_reduce
    cases x j <;> rfl

theorem witRe_blind : Spec.witRe_blind := fun _ _ _ _ _ _ => ⟨rfl, fun _ _ _ _ _ _ _ => rfl⟩

end Iop
