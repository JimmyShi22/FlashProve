-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecDecode.lean: this file is about knowledge soundness of the holographic interactive oracle
proof: an extractor for a session that reads the statement and the first reduction's transcript, and
no later witness.
In this library's words: the witness map of a session as a decoder: "the cells are the decoding,
with their samples, of the oracles of cells".

Definitions, statements and proofs.

Why: the witness map of the object with records (Hiop/RecBuild.lean: `S.wit`) decodes the oracles
that the preamble of a request leaves and then runs the preamble's extractor `cellsOf` backwards;
that extractor may read every verifier message of the preamble. An extractor of a compiled argument
wants less: a map that reads the oracles of cells, the seeds of their samples and the answers. No
new notion is needed for that. The item is the parameter list's own item on knowledge soundness of
the preamble (Hiop/RecSubs.lean: `PreKnowR`) at an extractor that ignores the later witness
(`S.PreKnowDec`).
Where it would come from (a sketch; no theorem of this file carries it out): if the preamble is a
chain (a sending with its sample, then a tail), if the tail's input statement names the oracle and
the sample, and if on collision-free statements its relaxed relation determines its witness (where
the sending is sound into these statements and pays for a collision in its own list:
Ior/KnowColl.lean: `KnowInto`; the tail is then asked on them only), then the tail's extractor may
be replaced by the decoder of that statement (Ior/KnowCollGood.lean: `goodT_of_det`), and then
`Spec.extSeq_dec` applies.

Main names:
  `S.PreKnowDec dC ε` := PreKnowR S.on S.req (the index decoder answers) C.RreqR (fun a τ _ => dC a
    τ) ε, dC : statement → the preamble's transcript → cells.
  `Spec.extSeq_dec`: the composed extractor (Ior/SeqProofs.lean: `IOR.extSeq`) of "R₁, then R₂" with
    the decoder of the middle statement in the second place reads neither the later witness nor the
    second part of the transcript.
  `Spec.soundAtR_conseq`, `Spec.soundR_conseq`, `Spec.propsR_conseq`: an object with records:
    another witness map that is valid wherever the old one is (where the index decodes with the
    record and the verifier accepts): then `SoundAtR`, `SoundR`, `PropsR` go over from the old map
    to it, same numbers.
  `S.withCells dC`: the same sub-protocols with the extractor fun a τ _ => dC a τ;
    `Spec.lhr_withCells`: the same object, by definition.
  `S.witDec dC`: the witness map fun a y τ => dC (a, y) (the preamble's part of τ): no default
    value, no case on the verifier's output.
  `Spec.rec_soundAt_dec`: index binding of the object with the witness map `S.witDec dC`, same
    numbers as `Spec.rec_soundAt` (Hiop/RecMain.lean): from `C.Props b eR`, the lists (`S.Hyp P`,
    whole) and the item `S.PreKnowDec dC P.req.err`.
  By parts:
    `decOf w`: dC from a map by parts w : WitP .. S.req.shape .. (oracles' symbols, plain parts,
      verifier messages of the preamble).
    `WitP.fstP w`, `Spec.witDec_parts`: then `S.witDec (decOf w)` is `witOf` of a map by parts on
      the session's shape, each part cut to the preamble's rounds.
    `Spec.witDec_blind`: if w is blind from round j on (it reads no verifier message of that round
      or of a later one: `WitP.BlindFrom`, Ior/KnowWidePass.lean), that map is blind from round j on
      and from the end of the preamble on.

Limits: the written compilation's witness extractor recomputes the cells from the extracted index
and the instance (Hiop/KnowWideRecompute.lean) and reads nothing of a transcript. So the item and
the map of this file are not what that compilation uses; they are a stronger extra at the level of
the IOP: a valid witness stands in what the prover sent. (That holds for a `dC` that reads only what
the prover sent, in the sense of `Spec.rec_soundAt_dec`, under the hypotheses of its statement.)
`S.wit` (Hiop/RecBuild.lean) runs the field `S.cellsOf` (Hiop/RecSubs.lean), and `S.witDec dC`
(Hiop/RecDecode.lean) runs its argument `dC`; by type `S.cellsOf` and `dC` may also read the slot's
statement (instance, record, encoded index) and the verifier's messages of the preamble.
Which map: any `dC` with the item (`S.PreKnowDec`); the decoding, with their samples, of the oracles
of cells, which the title names, is not built in this file. This file does not say that any preamble
has the item, or which rounds hold seeds. It says nothing on the compiled argument.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecSoundProof
import Ior.KnowWideParts

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- a map by parts on the first of two shapes, as a map by parts on both -/
def WitP.fstP {X W : Type} {E : ExtSpec} {s : Shape} (t : Shape) (w : WitP X E s W) :
    WitP X E (s ++ t) W :=
  fun x y o pl ρ => w x y (Orcs.fst o) (Plains.fst pl) (Rho.fst ρ)

namespace Spec

/-- With the decoder of the middle statement in the second place, the composed extractor reads
neither the later witness nor the second part of the transcript. -/
def extSeq_dec : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (dm : X₂ × E₂.Str → W₂)
      (d : W₁) (a : X₁ × E₁.Str) (τ τ' : Tr (R₁.shape ++ R₂.shape)) (w w' : W₃),
    Tr.fst τ = Tr.fst τ' →
    IOR.extSeq R₁ R₂ e₁ (fun b _ (_ : W₃) => dm b) d a τ w =
      IOR.extSeq R₁ R₂ e₁ (fun b _ (_ : W₃) => dm b) d a τ' w'

def soundAtR_conseq : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit wit' : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape),
    (∀ rec i x y τ, L.decodeIndex y rec = some i → L.onlineBatch.loc.accept (x, rec) y τ = true →
      Rno i x (wit (x, rec) y τ) → Rno i x (wit' (x, rec) y τ)) →
    L.SoundAtR Rno wit eR εT εL εB → L.SoundAtR Rno wit' eR εT εL εB

def soundR_conseq : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Rno : I → X → Wn → Prop)
      (wit wit' : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (εs : ℝ≥0∞),
    (∀ rec i x y τ, L.decodeIndex y rec = some i → L.onlineBatch.loc.accept (x, rec) y τ = true →
      Rno i x (wit (x, rec) y τ) → Rno i x (wit' (x, rec) y τ)) →
    L.SoundR Rno wit εs → L.SoundR Rno wit' εs

def propsR_conseq : Prop :=
  ∀ (I X Wn : Type) (L : HolographicProtocol I X) (Ryes Rno : I → X → Wn → Prop)
      (wit wit' : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (M : LH.Nums),
    (∀ rec i x y τ, L.decodeIndex y rec = some i → L.onlineBatch.loc.accept (x, rec) y τ = true →
      Rno i x (wit (x, rec) y τ) → Rno i x (wit' (x, rec) y τ)) →
    L.PropsR Ryes Rno wit M → L.PropsR Ryes Rno wit' M

/-- cut to the first part: if w is blind from round j on: blind from round `min j s.length` on -/
def blindFrom_fstP : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s t : Shape) (w : WitP X E s W) (j : ℕ),
    w.BlindFrom j → (w.fstP t).BlindFrom (min j s.length)

end Spec

theorem extSeq_dec : Spec.extSeq_dec := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ R₁ R₂ e₁ dm d a τ τ' w w' h
  simp only [IOR.extSeq, Reduction.extSeq, h]

theorem soundAtR_conseq : Spec.soundAtR_conseq := by
  intro I X Wn L Rno wit wit' eR εT εL εB hk h
  refine ⟨h.noneColl, h.rcd, h.sndT, h.sndL,
    fun rec => sndBKT_conseq X Wn Wn _ (L.batAt rec) L.maxBatchSize L.early L.late _ _ _ _ εB ?_ (h.sndB rec)⟩
  rintro x y τ ha (hw | ⟨i, hi, hw⟩)
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, hk rec i x y τ hi ha hw⟩

theorem soundR_conseq : Spec.soundR_conseq := by
  intro I X Wn L Rno wit wit' εs hk h
  obtain ⟨ε, hε, hB⟩ := h.sndB
  refine ⟨h.noneColl, h.rcd, h.sndT, h.sndL, ε, hε,
    fun rec => sndBKT_conseq X Wn Wn _ (L.batAt rec) L.maxBatchSize L.early L.late _ _ _ _ ε ?_ (hB rec)⟩
  rintro x y τ ha (hw | ⟨i, hi, hw⟩)
  · exact Or.inl hw
  · exact Or.inr ⟨i, hi, hk rec i x y τ hi ha hw⟩

theorem propsR_conseq : Spec.propsR_conseq := fun I X Wn L _ Rno wit wit' M hk h =>
  ⟨h.sub, soundR_conseq I X Wn L Rno wit wit' M.εs hk h.sound, h.honest⟩

/-- agreement before round min j |s| of s ++ t gives agreement of the first parts before round j -/
theorem Rho.AgreeTo.fst :
    ∀ {s : Shape} (t : Shape) (j : ℕ) {ρ ρ' : Rho (s ++ t)},
      Rho.AgreeTo (min j s.length) ρ ρ' → Rho.AgreeTo j (Rho.fst (s := s) ρ) (Rho.fst ρ')
  | [], _, _, _, _, _ => trivial
  | _ :: _, _, 0, _, _, _ => trivial
  | r :: s, t, j + 1, (c, ρ), (c', ρ'), h => by
      have e : min (j + 1) (r :: s).length = min j s.length + 1 := Nat.succ_min_succ j s.length
      rw [e] at h
      have h' : c = c' ∧ Rho.AgreeTo (min j s.length) ρ ρ' := h
      exact ⟨h'.1, Rho.AgreeTo.fst t j h'.2⟩

theorem blindFrom_fstP : Spec.blindFrom_fstP := fun _ _ _ _ t _ j h x y _ _ _ _ hρ =>
  h x y _ _ _ _ (Rho.AgreeTo.fst t j hρ)

end Iop

namespace Hiop
open Iop Prob
open scoped ENNReal

namespace SubsR
variable {C : ConfigurationWithOutOfDomainSample} (S : SubsR C)

/-- The item: the list's item on knowledge soundness of the preamble of a request, at an extractor
that ignores the later witness. -/
def PreKnowDec (dC : (C.X × C.Rec) × C.E0.Str → Tr S.req.shape → C.Cells) (ε : Err S.req.shape) :
    Prop :=
  PreKnowR S.on S.req (fun a => (C.D a.2 a.1.2).isSome) C.RreqR (fun a τ _ => dC a τ) ε

/-- the same sub-protocols with that extractor -/
def withCells (dC : (C.X × C.Rec) × C.E0.Str → Tr S.req.shape → C.Cells) : SubsR C :=
  { S with cellsOf := fun a τ _ => dC a τ }

/-- The witness map of a session as a decoder: dC on the slot's statement and the preamble's part of
its local transcript. -/
def witDec (dC : (C.X × C.Rec) × C.E0.Str → Tr S.req.shape → C.Cells) :
    C.X × C.Rec → C.E0.Str → Tr (S.req.shape ++ S.linOn.ior.shape) → C.Cells :=
  fun a y τ => dC (a, y) (Tr.fst τ)

/-- dC from a map by parts on the preamble's shape -/
def decOf (w : WitP (C.X × C.Rec) C.E0 S.req.shape C.Cells) :
    (C.X × C.Rec) × C.E0.Str → Tr S.req.shape → C.Cells :=
  fun a τ => witOf w a.1 a.2 τ

end SubsR

namespace Spec

/-- the extractor is no part of the object -/
def lhr_withCells : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (dC : (C.X × C.Rec) × C.E0.Str → Tr S.req.shape → C.Cells),
    (S.withCells dC).lhr = S.lhr

/-- Index binding of the object, the witness map a decoder. -/
def rec_soundAt_dec : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b eR : ℕ)
      (dC : (C.X × C.Rec) × C.E0.Str → Tr S.req.shape → C.Cells),
    C.Props b eR → S.Hyp P → S.PreKnowDec dC P.req.err →
    S.lhr.SoundAtR C.Rno (S.witDec dC) eR
      (Err.app P.wf.err P.linOff.err : Err (S.wf.shape ++ S.linOff.shape)) P.link.err
      (Err.app P.req.err P.linOn.err : Err (S.req.shape ++ S.linOn.ior.shape))

/-- by parts -/
def witDec_parts : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (w : WitP (C.X × C.Rec) C.E0 S.req.shape C.Cells),
    S.witDec (S.decOf w) = witOf (w.fstP S.linOn.ior.shape)

/-- If w reads no verifier message from round j on: none from round j on is read, and none from the
end of the preamble on. -/
def witDec_blind : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (w : WitP (C.X × C.Rec) C.E0 S.req.shape C.Cells) (j : ℕ),
    w.BlindFrom j → (w.fstP S.linOn.ior.shape).BlindFrom (min j S.req.shape.length)

end Spec

theorem lhr_withCells : Spec.lhr_withCells := fun _ _ _ => rfl

theorem rec_soundAt_dec : Spec.rec_soundAt_dec := by
  intro C S P b eR dC hC hS hD
  have hK : (S.withCells dC).HypK
      (⟨P.wf, P.linOff, P.link, P.req, P.linOn⟩ : (S.withCells dC).Nums) :=
    ⟨hS.know.wf, hS.know.linOff, hS.know.link, hD, hS.know.linOn⟩
  have hB := rec_online_know C (S.withCells dC) ⟨P.wf, P.linOff, P.link, P.req, P.linOn⟩
    hK hS.honest.req.passes hS.honest.req.copy
  have h0 := rec_soundAt C S P b eR hC hS
  refine ⟨h0.noneColl, h0.rcd, h0.sndT, h0.sndL,
    fun rec =>
      sndBKT_conseq C.X C.Cells C.Cells C.E0 (S.lhr.batAt rec) S.N id none _ _ _ _ _ ?_ (hB rec)⟩
  intro x y (τ : Tr (S.req.shape ++ S.linOn.ior.shape)) hacc hw
  have hacc' : ((S.req.out (x, rec) y (Tr.fst τ)).bind fun b =>
        S.linOn.ior.out b (S.req.imp y (Tr.fst τ)) (Tr.snd (s := S.req.shape) τ)).isSome = true :=
    hacc
  cases ho : S.req.out (x, rec) y (Tr.fst τ) with
  | none =>
    rw [ho] at hacc'
    cases hacc'
  | some b =>
    have e : (S.withCells dC).wit (x, rec) y τ = S.witDec dC (x, rec) y τ := by
      show witSeqT S.req (fun a τ _ => dC a τ)
          (fun a _ _ => S.on.decA S.dOn a.1.1 a.2) C.cells0 (x, rec) y τ =
        dC ((x, rec), y) (Tr.fst τ)
      simp only [witSeqT, ho]
    have hw' : C.D y rec = none ∨ ∃ i, C.D y rec = some i ∧ C.Rno i x (S.witDec dC (x, rec) y τ) :=
      e ▸ hw
    exact hw'

theorem witDec_parts : Spec.witDec_parts := by
  intro C S w
  funext a y τ
  show w a y (Tr.fst τ).read (Tr.fst τ).plains (Tr.fst τ).rho =
    w a y (Orcs.fst τ.read) (Plains.fst τ.plains) (Rho.fst τ.rho)
  rw [Tr.plains_fst, Tr.rho_fst, Orcs.fst_read]

theorem witDec_blind : Spec.witDec_blind := fun _ S w j h =>
  blindFrom_fstP _ _ _ S.req.shape S.linOn.ior.shape w j h

end Hiop
