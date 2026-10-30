-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/KnowWide.lean: this file is about knowledge soundness of the interactive oracle proof, before
it is compiled: it lets the extractor read, beside the instance, the encoded index and the whole
transcript of that instance, not the prover's oracles alone.

Definitions, statements and proofs. The wide forms of Hiop/Interface.lean (`SoundK`, `PropsK`) and
Hiop/GrindK.lean (`SoundAtK`, `SoundKG`, `PropsNoAccK`); these five are the instance "forget". A
witness map is the extractor named in round-by-round knowledge soundness for the instances of a
batch (`SndBKT`, Ior/KnowWide.lean).

Hiop/Interface.lean's witness map wit : X → Orcs s → W reads a witness off an instance and the
symbols of the prover's oracles of a full local transcript of a session. Here (Ior/KnowWide.lean
says why):
  wit : X → (encoded index) → Tr L.onlineBatch.loc.shape → W: the instance; the encoded index on which the
  session runs; the slot's whole local transcript: oracles, plain parts, its own and the shared
  verifier messages. Not another slot's.

Main names:
  `BatchProtocol.SoundKT L Rno wit εs`; `SoundAtKT .. εT εL εB` (three explicit lists);
    `SoundKGT .. gT gL gB c` (`SoundAtKT` at some lists that c bounds, given the bits gT, gL, gB;
    exactly: its docstring); `PropsKT`, `PropsNoAccKT` (with `BatchProtocol.Props`, `BatchProtocol.PropsNoAcc` for the
    two languages).
  `Spec.soundK_iff_T`, `Spec.soundAtK_iff_T`, `Spec.soundKG_iff_T`, `Spec.propsK_iff_T`,
    `Spec.propsNoAccK_iff_T`: each of these five notions is the wide one at
    fun x _ τ => wit x τ.read.
  `Spec.sound_of_soundKT`: `SoundKT` gives the soundness that the interface requires, for the
    language of the relation.
  `Spec.soundKT_iff_at`, `Spec.soundKGT_of_soundKT`, `Spec.soundKGT_zero`: as in Hiop/GrindK.lean.
  `Spec.soundAtKT_conseq`: `SoundAtKT` goes over, with the same lists, to another witness map that
    is valid wherever the old one is (where the index decodes and the verifier accepts).
  `Spec.soundAtKT_of_det`, `Spec.soundKT_of_det`, `Spec.propsKT_of_det`: narrowing at the interface:
    if, where the encoded index decodes to i and the verifier accepts, the relation determines its
    witness from what d reads (Rno i x w → w = d x y τ), wit may be replaced by d.
    How little that is: Rno names no oracle, so the premise holds only where, at every (i, x) with
    an accepted transcript on an encoded index that decodes to i, the witness is a function of index
    and instance (d = "recompute the cells from the index"). (For that map less is enough, "the
    recomputed witness is valid whenever some witness is", and it is the map of the written
    compilation: Hiop/KnowWideRecompute.lean.) It does not give "the member of the list that agrees
    with the sample": a transcript accepted by luck may hold other cells.
    That narrowing is made one level lower, at relations that name oracles and samples
    (Ior/KnowColl.lean: `know_of_det`; Ior/KnowCollGood.lean: `goodT_of_det`; Ior/KnowWide.lean:
    `sndBKT_of_det` at a batch IOP with the slots' oracles in the instance), and then composed.

Limits: this file says nothing on whether any interface has the properties. It says nothing on the
compiled argument: how an extractor learns verifier messages is the compiler's matter. It says
nothing on the passes (blocks, tests, cuts and joins): CompileK/KnowWidePass.lean,
Ior/KnowWidePass.lean.

Terms: lean/GLOSSARY.md.
-/
import Hiop.GrindK
import Ior.KnowWide

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

variable {I X Wn : Type}

/-- the relation of a session on (instance, encoded index, witness) -/
def BatchProtocol.relB (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) : X → (oneExternalString L.wordLength L.Symbol).Str → Wn → Prop :=
  fun x y w => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x w

/-- Index-binding round-by-round knowledge soundness, wide witness map. -/
structure BatchProtocol.SoundKT (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞) : Prop where
  sndT : ∃ ε, Err.Below ε εs ∧ L.offline.Sound (fun _ y => L.decodeIndex y ≠ none) ε
  sndL : ∃ ε, Err.Below ε εs ∧ L.link.Sound (fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) ε
  sndB : ∃ ε, Err.Below ε εs ∧ L.onlineBatch.SndBKT L.maxBatchSize L.early L.late (L.relB Rno) wit ε

/-- the same for three explicit lists of errors -/
structure BatchProtocol.SoundAtKT (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape)
    (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) : Prop where
  sndT : L.offline.Sound (fun _ y => L.decodeIndex y ≠ none) εT
  sndL : L.link.Sound (fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) εL
  sndB : L.onlineBatch.SndBKT L.maxBatchSize L.early L.late (L.relB Rno) wit εB

/-- Some three lists of errors satisfy `SoundAtKT`, and each entry of them, read as a probability,
is ≤ c · 2^b, where b is what gT, gL or gB gives as the bits of work of the entry's round
(`Err.BelowG`, Iop/Grind.lean) -/
def BatchProtocol.SoundKGT (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞) : Prop :=
  ∃ εT εL εB,
    L.SoundAtKT Rno wit εT εL εB ∧ Err.BelowG gT εT c ∧ Err.BelowG gL εL c ∧ Err.BelowG gB εB c

/-- All properties, with a witness, wide witness map. -/
structure BatchProtocol.PropsKT (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums) : Prop where
  props   : L.Props (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) M
  soundKT : L.SoundKT Rno wit M.εs

/-- all properties but acceptance -/
structure BatchProtocol.PropsNoAccKT (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums) : Prop where
  props   : L.PropsNoAcc (fun i x => ∃ w, Ryes i x w) (fun i x => ∃ w, Rno i x w) M
  soundKT : L.SoundKT Rno wit M.εs

namespace Spec

def soundK_iff_T : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundK Rno wit εs ↔ L.SoundKT Rno (fun x _ τ => wit x τ.read) εs

def soundAtK_iff_T : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    L.SoundAtK Rno wit εT εL εB ↔ L.SoundAtKT Rno (fun x _ τ => wit x τ.read) εT εL εB

def soundKG_iff_T : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞),
    L.SoundKG Rno wit gT gL gB c ↔ L.SoundKGT Rno (fun x _ τ => wit x τ.read) gT gL gB c

def propsK_iff_T : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums),
    L.PropsK Ryes Rno wit M ↔ L.PropsKT Ryes Rno (fun x _ τ => wit x τ.read) M

def propsNoAccK_iff_T : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit : X → Orcs L.onlineBatch.loc.shape → Wn) (M : LH.Nums),
    L.PropsNoAccK Ryes Rno wit M ↔ L.PropsNoAccKT Ryes Rno (fun x _ τ => wit x τ.read) M

def sound_of_soundKT : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundKT Rno wit εs → L.Sound (fun i x => ∃ w, Rno i x w) εs

def soundKT_iff_at : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundKT Rno wit εs ↔
    ∃ εT εL εB, L.SoundAtKT Rno wit εT εL εB ∧ Err.Below εT εs ∧ Err.Below εL εs ∧ Err.Below εB εs

def soundKGT_of_soundKT : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    L.SoundKT Rno wit εs →
    ∀ (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape),
      L.SoundKGT Rno wit gT gL gB εs

def soundKGT_zero : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (c : ℝ≥0∞),
    L.SoundKGT Rno wit (GBits.zero _) (GBits.zero _) (GBits.zero _) c ↔ L.SoundKT Rno wit c

/-- another witness map that is valid wherever the old one is -/
def soundAtKT_conseq : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit wit' : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    (∀ i x y τ, L.decodeIndex y = some i → L.onlineBatch.loc.accept x y τ = true →
      Rno i x (wit x y τ) → Rno i x (wit' x y τ)) →
    L.SoundAtKT Rno wit εT εL εB → L.SoundAtKT Rno wit' εT εL εB

/-- Narrowing, for explicit lists. -/
def soundAtKT_of_det : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit d : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εT : Err L.offline.shape)
      (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    (∀ i x y τ w, L.decodeIndex y = some i → L.onlineBatch.loc.accept x y τ = true → Rno i x w → w = d x y τ) →
    L.SoundAtKT Rno wit εT εL εB → L.SoundAtKT Rno d εT εL εB

def soundKT_of_det : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop)
      (wit d : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    (∀ i x y τ w, L.decodeIndex y = some i → L.onlineBatch.loc.accept x y τ = true → Rno i x w → w = d x y τ) →
    L.SoundKT Rno wit εs → L.SoundKT Rno d εs

def propsKT_of_det : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit d : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums),
    (∀ i x y τ w, L.decodeIndex y = some i → L.onlineBatch.loc.accept x y τ = true → Rno i x w → w = d x y τ) →
    L.PropsKT Ryes Rno wit M → L.PropsKT Ryes Rno d M

end Spec

theorem soundK_iff_T : Spec.soundK_iff_T := fun _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.sndT, h.sndL, h.sndB⟩, fun h => ⟨h.sndT, h.sndL, h.sndB⟩⟩

theorem soundAtK_iff_T : Spec.soundAtK_iff_T := fun _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.sndT, h.sndL, h.sndB⟩, fun h => ⟨h.sndT, h.sndL, h.sndB⟩⟩

theorem soundKG_iff_T : Spec.soundKG_iff_T := fun I X Wn L Rno wit _ _ _ _ =>
  ⟨fun ⟨εT, εL, εB, h, b⟩ => ⟨εT, εL, εB, (soundAtK_iff_T I X Wn L Rno wit εT εL εB).1 h, b⟩,
    fun ⟨εT, εL, εB, h, b⟩ => ⟨εT, εL, εB, (soundAtK_iff_T I X Wn L Rno wit εT εL εB).2 h, b⟩⟩

theorem propsK_iff_T : Spec.propsK_iff_T := fun I X Wn L _ Rno wit M =>
  ⟨fun h => ⟨h.props, (soundK_iff_T I X Wn L Rno wit M.εs).1 h.soundK⟩,
    fun h => ⟨h.props, (soundK_iff_T I X Wn L Rno wit M.εs).2 h.soundKT⟩⟩

theorem propsNoAccK_iff_T : Spec.propsNoAccK_iff_T := fun I X Wn L _ Rno wit M =>
  ⟨fun h => ⟨h.props, (soundK_iff_T I X Wn L Rno wit M.εs).1 h.soundK⟩,
    fun h => ⟨h.props, (soundK_iff_T I X Wn L Rno wit M.εs).2 h.soundKT⟩⟩

theorem sound_of_soundKT : Spec.sound_of_soundKT := by
  intro I X Wn L Rno wit εs hK
  refine ⟨hK.sndT, hK.sndL, ?_⟩
  obtain ⟨ε, hε, hB⟩ := hK.sndB
  refine ⟨ε, hε, sndBL_of_sndBP X _ L.onlineBatch L.maxBatchSize L.early L.late _ _ ε ?_ hB⟩
  rintro x y τ (hw | ⟨i, hi, hw⟩)
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, _, hw⟩

theorem soundKT_iff_at : Spec.soundKT_iff_at := by
  intro I X Wn L Rno wit εs
  constructor
  · rintro ⟨⟨εT, bT, hT⟩, ⟨εL, bL, hL⟩, ⟨εB, bB, hB⟩⟩
    exact ⟨εT, εL, εB, ⟨hT, hL, hB⟩, bT, bL, bB⟩
  · rintro ⟨εT, εL, εB, h, bT, bL, bB⟩
    exact ⟨⟨εT, bT, h.sndT⟩, ⟨εL, bL, h.sndL⟩, ⟨εB, bB, h.sndB⟩⟩

theorem soundKGT_of_soundKT : Spec.soundKGT_of_soundKT := by
  intro I X Wn L Rno wit εs h gT gL gB
  obtain ⟨εT, εL, εB, hA, bT, bL, bB⟩ := (soundKT_iff_at I X Wn L Rno wit εs).1 h
  exact ⟨εT, εL, εB, hA, Err.BelowG.of_below gT bT,
    Err.BelowG.of_below gL bL, Err.BelowG.of_below gB bB⟩

theorem soundKGT_zero : Spec.soundKGT_zero := by
  intro I X Wn L Rno wit c
  rw [soundKT_iff_at I X Wn L Rno wit c]
  constructor
  · rintro ⟨εT, εL, εB, hA, bT, bL, bB⟩
    exact ⟨εT, εL, εB, hA, (Err.belowG_zero εT c).1 bT,
      (Err.belowG_zero εL c).1 bL, (Err.belowG_zero εB c).1 bB⟩
  · rintro ⟨εT, εL, εB, hA, bT, bL, bB⟩
    exact ⟨εT, εL, εB, hA, (Err.belowG_zero εT c).2 bT,
      (Err.belowG_zero εL c).2 bL, (Err.belowG_zero εB c).2 bB⟩

theorem soundAtKT_conseq : Spec.soundAtKT_conseq := by
  intro I X Wn L Rno wit wit' εT εL εB hk h
  refine ⟨h.sndT, h.sndL,
    sndBKT_conseq X Wn Wn _ L.onlineBatch L.maxBatchSize L.early L.late _ _ wit wit' εB ?_ h.sndB⟩
  rintro x y τ ha (hw | ⟨i, hi, hw⟩)
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, hk i x y τ hi ha hw⟩

theorem soundAtKT_of_det : Spec.soundAtKT_of_det := fun I X Wn L Rno wit d εT εL εB hd h =>
  soundAtKT_conseq I X Wn L Rno wit d εT εL εB
    (fun i x y τ hi ha hw => hd i x y τ _ hi ha hw ▸ hw) h

theorem soundKT_of_det : Spec.soundKT_of_det := by
  intro I X Wn L Rno wit d εs hd h
  obtain ⟨εT, εL, εB, hA, b⟩ := (soundKT_iff_at I X Wn L Rno wit εs).1 h
  exact (soundKT_iff_at I X Wn L Rno d εs).2
    ⟨εT, εL, εB, soundAtKT_of_det I X Wn L Rno wit d εT εL εB hd hA, b⟩

theorem propsKT_of_det : Spec.propsKT_of_det := fun I X Wn L _ Rno wit d M hd h =>
  ⟨h.props, soundKT_of_det I X Wn L Rno wit d M.εs hd h.soundKT⟩

end Iop
