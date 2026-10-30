-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/WideLang.lean: an interface whose witness map reads the whole local
transcript: from the wide notions to the idle relations.





Definitions, statements and proofs: one lemma on the interface.





Why: the bundle `BatchProtocol.PropsK` has index-binding round-by-round knowledge soundness whose
witness map has two arguments, the instance and the oracles of the prover. Once decoding is not
unique, the blocks' extractors go backwards, and what they read includes plain parts and verifier
messages. That case is covered by the interface's wide notion (Ior/KnowWide.lean,
Hiop/KnowWide.lean: `SndBKT`, `BatchProtocol.SoundKT`, `BatchProtocol.PropsKT`).
An extractor of the compiled argument is handed the key, the committer's trace, the instance, the
proof and the prover's trace: not the verifier's queries. So a wide map cannot simply be put into
the named witness extractor. For a relation with an idle witness it need not be: the binding clause
then reads the index extractor alone, and the session's witness map is used only to know that a
witness exists.

Main names, each statement under its hypotheses:
  `idleRel Wn R` (Hiop/KnowWideIdle.lean): the relation on (index, instance, w : Wn) that holds if R
    has some witness; w is idle.
  `Spec.propsKW_idle`, and in Hiop/KnowWideIdle.lean `Spec.soundAtK_idle_of_T`,
    `Spec.soundK_idle_of_T`, `Spec.soundKG_idle_of_T`, `Spec.propsK_idle_of_T`: the lemma: the wide
    notions for (Ryes, Rno, wit) give the notions with a witness map on oracles (`BatchProtocol.PropsK`,
    Hiop/Interface.lean; `BatchProtocol.PropsKW`) for the idle relations with a constant witness map (the goal
    "the index does not decode, or some witness exists" is weaker: `sndBKT_conseq`,
    Ior/KnowWide.lean).
  `BatchProtocol.PropsKWT`: all properties but for zero knowledge, wide (the twin of `BatchProtocol.PropsKW`,
    CompileK/WholePullMain.lean). `SoundOT`: the hypothesis on soundness with work, wide (True if
    there is no work).







  Wi is the witness type of the interface's
  relations, Wn that of the scheme's syntax; they need not be the same.

Limits: no witness is extracted: the idle relation
does not look at it.

The forms with a witness (cells; two relations) for a wide map are another matter: there the
extractor must learn verifier messages from the traces (CompileK/KnowExtT.lean). This holds of the
forms in which the extractor runs a wide map that reads verifier messages; the extractor that
recomputes the witness reads no verifier message (CompileK/Recompute.lean).
The index decoder is the interface's `L.decodeIndex`, which reads the encoded index and nothing else. What
the heads of CompileK/Main.lean and CompileK/GrindMain.lean
list as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import CompileK.GrindOpt
import CompileK.GrindWhole
import CompileK.WholePullMain
import CompileK.Main
import CompileK.Glue
import CompileK.GenWitProofs
import CompileK.KnowPull
import CompileK.KnowLocal
import CompileK.KnowBinding
import CompileK.KnowBindingUp
import Top.Extraction
import ZKCP.ExtractionMaps
import Hiop.KnowWideIdle

set_option autoImplicit false

namespace Iop
open scoped ENNReal

variable {I X Wi : Type}

/-- All properties with a witness, but for zero knowledge; wide witness map. -/
structure BatchProtocol.PropsKWT (L : BatchProtocol I X) (Ryes Rno : I → X → Wi → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (M : LH.Nums) : Prop where
  sub      : ∀ i x, (∃ w, Ryes i x w) → ∃ w, Rno i x w
  wired    : L.Wired
  soundKT  : L.SoundKT Rno wit M.εs
  complete : L.Complete (fun i x => ∃ w, Ryes i x w) M.pT M.pL M.pO
  localT   : L.offline.IsLocal
  localL   : L.link.IsLocal
  localB   : L.onlineBatch.loc.IsLocal
  cohB     : L.onlineBatch.ann.Coherent
  pointT   : Nonempty L.offline.shape.IsPoint
  pointL   : Nonempty L.link.shape.IsPoint
  pointB   : Nonempty L.onlineBatch.loc.shape.IsPoint

theorem BatchProtocol.PropsKT.toKWT {L : BatchProtocol I X} {Ryes Rno : I → X → Wi → Prop}
    {wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi}
    {M : LH.Nums} (h : L.PropsKT Ryes Rno wit M) : L.PropsKWT Ryes Rno wit M :=
  ⟨h.props.sub, h.props.wired, h.soundKT, h.props.complete, h.props.localT, h.props.localL,
    h.props.localB, h.props.cohB, h.props.pointT, h.props.pointL, h.props.pointB⟩

namespace Spec

def propsKW_idle : Prop :=
  ∀ (I X Wi Wn : Type) (L : BatchProtocol I X) (Ryes Rno : I → X → Wi → Prop)
      (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (M : LH.Nums) (w0 : Wn),
    L.PropsKWT Ryes Rno wit M → L.PropsKW (idleRel Wn Ryes) (idleRel Wn Rno) (fun _ _ => w0) M

end Spec

theorem propsKW_idle : Spec.propsKW_idle := by
  intro I X Wi Wn L Ryes Rno wit M w0 h
  refine ⟨fun i x ⟨_, hy⟩ => ⟨w0, h.sub i x hy⟩, h.wired,
    soundK_idle_of_T I X Wi Wn L Rno wit M.εs h.soundKT w0, ?_, h.localT, h.localL, h.localB,
    h.cohB, h.pointT, h.pointL, h.pointB⟩
  rw [idleRel_lang Ryes w0]
  exact h.complete

end Iop

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Top.Batch Top.ProgDraw Hiop
open Compile.BatchLife (Sims)
open scoped ENNReal

/-- Every round has error at most c, counting its work; wide witness map (True if there is no work).
-/
def SoundOT {I X Wi Nn : Type} {L : BatchProtocol I X} (Rno : I → X → Wi → Prop)
    (wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi) (c : ℝ≥0∞) : Option (Work Nn L) → Prop
  | none => True
  | some w => L.SoundKGT Rno wit w.gT w.gL w.gB c

theorem SoundOT.idle {I X Wi Wn Nn : Type} {L : BatchProtocol I X} {Rno : I → X → Wi → Prop}
    {wit : X → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wi} {c : ℝ≥0∞} (w0 : Wn) :
    ∀ {o : Option (Work Nn L)}, SoundOT Rno wit c o → SoundO (idleRel Wn Rno) (fun _ _ => w0) c o
  | none, _ => trivial
  | some w, h => soundKG_idle_of_T I X Wi Wn L Rno wit w.gT w.gL w.gB c h w0

end Compile.Batch
