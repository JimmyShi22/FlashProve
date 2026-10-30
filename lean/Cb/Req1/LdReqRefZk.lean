-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefZk.lean: the reference request: what zero knowledge, beside its hypotheses
(`r.Hyp`), the format (`r.chain.Fmt`) and the bound on the errors (`r.Below κ`: on the numbers in
each link's data field `l.P.err`) ask, segment by segment (what zero knowledge asks of the request
beside `r.Hyp`: `r.Zk`, a premise of `Spec.ldReq_goodT`, Cb/Req1/LdReq.lean).

Book-keeping for a composed reduction: three conditions on the chain of the reference request are
brought down to conditions on its parts.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs. Framework only: it carries the
three notions through the constructions of Cb/Req1/LdReqRef.lean (`LdSeg.pre`, `LdRefL.segs`,
`ldReqRef`).
The three notions, of a move, a list of moves, a segment, a request: `Zk base` with `After base`,
over sets of facts (`MaskFact`, Cb/Req1/LdSegFresh.lean), Cb/Req1/LdReq.lean; `Fmt φ ψ`, between
formats of joints (`JFmt`, Cb/Req1/LdReqFormat.lean), Cb/Req1/LdSegFormat.lean; `Below κ` (of a
move: `m.chain.ErrBelow κ`), Cb/Req1/LdReqBelow.lean. r is the reference request
`ldReqRef R first a₁ more hm b L T`, with its list L of segments S and its last segment T
(Cb/Req1/LdReqRef.lean). A `MaskFact W` is a reading `kc` of witnesses of type W into a type `Kc`, a
finite, non-empty type `Mk`, and a map `put : Mk → Kc → Kc`.

Main names:
  For a segment with a step at its head (`s.pre en he`):
    `Spec.ldReqRefK_after`: what is fresh after it, given "base", is what is fresh after s, given
      what is fresh after the step.
    `Spec.ldReqRefK_zk`: zero knowledge asks of it what it asks of s there: the step asks nothing,
      beside its hypotheses; in this sense: `s.Zk (en.After base) → (s.pre en he).Zk base`.
  For the list of reference segments: `L.Zk base`, `L.Fmt φ ψ`, `L.Below κ`: by recursion, in terms
  of the reference segments themselves (`S.K.seg S.l S.Qc`) and the entry steps.
    `Spec.ldReqRefK_segs`, `Spec.ldReqRefK_segsFmt`: these give `L.segs.Zk base`, `L.segs.Below κ`;
      `L.segs.Fmt φ ψ`.
  `Spec.ldReqRefK_req`: for the request, under `[CharP E pp]`, `T.OK pp`, `2 ≤ R.n`, `R.Z.OK`,
    `R.Tie`: `r.Zk` from: `L.Zk` at the facts that are fresh behind the first sendings; the last
    segment's body at the facts that are fresh behind the segments and its entry step; the places of
    the final batching's own masks; its fact is fresh before it.
  `Spec.ldReqRefK_reqFmt`: `r.chain.Fmt`, up to the object's format at the last stage, from the
    formats of the first sendings, of the list, of the last segment's entry step, body and exit
    step. The last three moves have theirs (Cb/Obj/LdObjectReqEndFmt.lean).
  `Spec.ldReqRefK_reqBelow`: `r.Below κ` from the parts'; steps have no round.

Limits: this file does not say what a reference segment's own `Zk`, `Fmt`, `Below` ask
(Cb/Req1/LdSegRef*.lean, Cb/Req1/LdSegWhole*.lean, Cb/Req1/LdSegFront*.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRef
import Cb.Req1.LdReqBelow
import Cb.Req1.LdSegFrontFmt
import Cb.Obj.LdObjectReqEndFmt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

namespace LdRefL
variable {E Kc : Type} [Field E] [Fintype E] {I : LdRefIx E} {a : LdStage E Kc}

/-- What zero knowledge asks of the list, beside its hypotheses, in terms of the reference
segments. -/
def Zk (base : MaskFact a.J.W → Prop) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Zk base ∧ (S.K.seg S.l S.Qc).Zk (S.entry.After (L.segs.After base))

def Below (κ : ℝ≥0∞) : {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.Below κ ∧ (S.K.seg S.l S.Qc).Below κ

/-- The list has the format, in terms of the reference segments and the entry steps. -/
def Fmt {E0 : ExtSpec} {Rc Pw : Type} (φ : JFmt Kc E0 Rc Pw a.J) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → JFmt Kc E0 Rc Pw b.J → Prop
  | _, .nil, ψ => φ = ψ
  | _, .snoc (b := b) L S, ψ =>
    ∃ (χ : JFmt Kc E0 Rc Pw b.J) (χ' : JFmt Kc E0 Rc Pw S.A.V.Fp.s0.J),
      L.Fmt φ χ ∧ S.entry.Fmt χ χ' ∧ (S.K.seg S.l S.Qc).Fmt χ' ψ

end LdRefL

namespace Spec

def ldReqRefK_after : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a a₀ d : LdStage E Kc) (s : LdSeg a₀ d) (en : LdMv a a₀)
      (he : en.tag = .step) (base : MaskFact a.J.W → Prop),
    (s.pre en he).After base = s.After (en.After base)

def ldReqRefK_zk : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a a₀ d : LdStage E Kc) (s : LdSeg a₀ d) (en : LdMv a a₀)
      (he : en.tag = .step) (base : MaskFact a.J.W → Prop),
    s.Zk (en.After base) → (s.pre en he).Zk base

def ldReqRefK_fmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a a₀ d : LdStage E Kc)
      (s : LdSeg a₀ d) (en : LdMv a a₀) (he : en.tag = .step) (φ : JFmt Kc E0 Rc Pw a.J)
      (χ : JFmt Kc E0 Rc Pw a₀.J) (ψ : JFmt Kc E0 Rc Pw d.J),
    en.Fmt φ χ → s.Fmt χ ψ → (s.pre en he).Fmt φ ψ

def ldReqRefK_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (a a₀ d : LdStage E Kc) (s : LdSeg a₀ d) (en : LdMv a a₀)
      (he : en.tag = .step) (κ : ℝ≥0∞),
    en.chain.ErrBelow κ → s.Below κ → (s.pre en he).Below κ

def ldReqRefK_segs : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (I : LdRefIx E)
      (a b : LdStage E Kc) (L : LdRefL E Kc I a b),
    (∀ base, L.Zk base → L.segs.Zk base) ∧ (∀ κ, L.Below κ → L.segs.Below κ)

def ldReqRefK_segsFmt : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (I : LdRefIx E) (a b : LdStage E Kc) (L : LdRefL E Kc I a b)
      (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J),
    L.Fmt φ ψ → L.segs.Fmt φ ψ

/-- Every move as the sub-protocol of its own chain: the same format. -/
def ldReqRefK_asSub : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a b : LdStage E Kc)
      (p : LdProg a b) (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J),
    p.Fmt φ ψ → p.asSub.Fmt φ ψ

/-- States, under the hypotheses below: the request has the format, up to the object's format at the
last stage. -/
def ldReqRefK_reqFmt : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc) (more : LdProg first.tgt a₁)
      (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc) (L : LdRefL E Kc R.ix a₁ b)
      (T : LdRefT R b) (q : Finset R.z.J.E.Pos → Prop)
      (φ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx a.J)
      (φ₀ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx first.tgt.J)
      (φ₁ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx a₁.J)
      (φb : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx b.J)
      (χ : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx T.A.V.Fp.s0.J)
      (χ' : JFmt Kc R.Cf.conf.E0 R.Cf.conf.Rec R.Cf.conf.PIdx (T.A.X.tgt T.St₁ T.Az).J),
    first.link.Fmt φ φ₀ → more.Fmt φ₀ φ₁ → L.Fmt φ₁ φb →
    T.entry.Fmt φb χ → (T.A.body T.St₁ T.fz T.Az).Fmt χ χ' →
    T.exit.Fmt χ'
      (R.X.src.fmt (⟨id, id⟩ : IxAt R.Cf.conf.E0 R.Cf.conf.E0) (fun x => R.rc x.2.2) Prod.fst q) →
    (ldReqRef R first a₁ more hm b L T).chain.Fmt φ (R.O.fmtZAt R.bEnd Prod.fst q)

/-- States, under the hypotheses below: `(ldReqRef R first a₁ more hm b L T).Below κ`. -/
def ldReqRefK_reqBelow : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc) (more : LdProg first.tgt a₁)
      (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc) (L : LdRefL E Kc R.ix a₁ b)
      (T : LdRefT R b) (κ : ℝ≥0∞),
    Err.Below first.link.P.err κ → more.Below κ → L.Below κ → (T.A.body T.St₁ T.fz T.Az).Below κ →
    Err.Below R.X.link.P.err κ → (ldReqRef R first a₁ more hm b L T).Below κ

/-- States, under the hypotheses below: `(ldReqRef R first a₁ more hm b L T).Zk`. -/
def ldReqRefK_req : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (pp : ℕ) [CharP E pp]
      (R : LdORE F E Kc) (a : LdStage E Kc) (first : LdSendD a) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (L : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b),
    T.OK pp → 2 ≤ R.n → R.Z.OK → R.Tie → R.X.Own → L.Zk (ldReqRef R first a₁ more hm b L T).base₀ →
    (T.A.body T.St₁ T.fz T.Az).Zk
      (T.entry.After (L.segs.After (ldReqRef R first a₁ more hm b L T).base₀)) →
    R.X.stepIn.After (T.tail.After (L.segs.After (ldReqRef R first a₁ more hm b L T).base₀))
      R.X.mask.fact →
    (ldReqRef R first a₁ more hm b L T).Zk

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- A move of the kind "step" asks nothing, beside its hypotheses. -/
theorem LdMv.zk_of_step {a b : LdStage E Kc} (m : LdMv a b)
    (h : m.tag = .step) (base : MaskFact a.J.W → Prop) : m.Zk base := by
  have := ldReq_zk_free E Kc a b ((LdProg.nil a).snoc m) base
    ((LdProg.all_snoc _ _ _).2
      ⟨LdProg.all_nilK _ _,
        by rw [h]; exact ⟨fun e => LdTag.noConfusion e, fun e => LdTag.noConfusion e⟩⟩)
  have h2 := ((LdProg.zk_snoc _ _ _).1 this).2
  rwa [LdProg.after_nil] at h2

theorem LdProg.head_after {a a₀ b : LdStage E Kc} (en : LdMv a a₀)
    (p : LdProg a₀ b) (base : MaskFact a.J.W → Prop) :
    (((LdProg.nil a).snoc en).app p).After base = p.After (en.After base) := by
  rw [ldProg_app_after, LdProg.after_snoc, LdProg.after_nil]

end

theorem ldReqRefK_after : Spec.ldReqRefK_after := by
  intro E Kc _ _ a a₀ d s en he base
  show s.loc.After
      ((Chain.one s.snd.link).FreshGiven
        (s.fold.After (s.bat.After ((((LdProg.nil a).snoc en).app s.body).After base)))) = _
  rw [LdProg.head_after]
  rfl

theorem ldReqRefK_zk : Spec.ldReqRefK_zk := by
  intro E Kc _ _ a a₀ d s en he base h
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (((LdProg.nil a).snoc en).app s.body).Zk base
    refine (ldProg_app_zk E Kc _ _ _ _ _ _).2
      ⟨(LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, en.zk_of_step he _⟩, ?_⟩
    rw [LdProg.after_snoc, LdProg.after_nil]
    exact h.body
  · show s.bat.Zk ((((LdProg.nil a).snoc en).app s.body).After base)
    rw [LdProg.head_after]
    exact h.bat
  · show s.fold.Zk (s.bat.After ((((LdProg.nil a).snoc en).app s.body).After base))
    rw [LdProg.head_after]
    exact h.fold
  · show s.loc.Zk
      ((Chain.one s.snd.link).FreshGiven
        (s.fold.After (s.bat.After ((((LdProg.nil a).snoc en).app s.body).After base))))
    rw [LdProg.head_after]
    exact h.loc

theorem ldReqRefK_fmt : Spec.ldReqRefK_fmt := by
  intro E Kc _ _ E0 Rc Pw a a₀ d s en he φ χ ψ h1 ⟨φb, φb₁, φc, φs, b1, b2, b3, b4, b5⟩
  exact ⟨φb, φb₁, φc, φs,
    ldProg_app_fmt E Kc E0 Rc Pw _ _ _ _ _ φ χ φb
      ((LdProg.fmt_snoc _ _ _ _).2 ⟨φ, (LdProg.fmt_nil _ _ _).2 rfl, h1⟩) b1,
    b2, b3, b4, b5⟩

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem LdProg.below_app {a b c : LdStage E Kc} (p : LdProg a b) (q : LdProg b c)
    (κ : ℝ≥0∞) (hp : p.Below κ) :
    q.Below κ → (p.app q).Below κ := by
  induction q with
  | nil => intro _; rw [LdProg.app_nil]; exact hp
  | snoc q m ih =>
      intro h
      rw [LdProg.app_snoc]
      exact (LdProg.below_snoc _ _ _).2
        ⟨ih ((LdProg.below_snoc q m κ).1 h).1, ((LdProg.below_snoc q m κ).1 h).2⟩

end

theorem ldReqRefK_below : Spec.ldReqRefK_below := fun _ _ _ _ a _ _ s en _ κ h1 h =>
  ⟨LdProg.below_app _ s.body κ
      ((LdProg.below_snoc _ _ _).2 ⟨by rw [LdProg.Below]; trivial, h1⟩) h.body,
    h.bat, h.fold, h.snd, h.loc⟩

theorem ldReqRefK_segs : Spec.ldReqRefK_segs := by
  intro E Kc _ _ I a b L
  induction L with
  | nil =>
    exact ⟨fun _ _ => by rw [LdRefL.segs, LdSegs.Zk]; trivial,
      fun _ _ => by rw [LdRefL.segs, LdSegs.Below]; trivial⟩
  | snoc L S ih =>
      refine ⟨fun base h => ?_, fun κ h => ?_⟩
      · rw [LdRefL.Zk] at h
        rw [LdRefL.segs, LdSegs.Zk]
        exact ⟨ih.1 base h.1, ldReqRefK_zk E Kc _ _ _ (S.K.seg S.l S.Qc) S.entry rfl _ h.2⟩
      · rw [LdRefL.Below] at h
        rw [LdRefL.segs, LdSegs.Below]
        exact ⟨ih.2 κ h.1,
          ldReqRefK_below E Kc _ _ _ (S.K.seg S.l S.Qc) S.entry rfl κ
            ((errBelow_one _ κ).2 trivial) h.2⟩

theorem ldReqRefK_segsFmt : Spec.ldReqRefK_segsFmt := by
  intro E Kc _ _ E0 Rc Pw I a b L φ
  induction L with
  | nil => intro ψ h; rw [LdRefL.Fmt] at h; rw [LdRefL.segs]; exact (LdSegs.fmt_nil _ _ _).2 h
  | snoc L S ih =>
      intro ψ h
      rw [LdRefL.Fmt] at h
      obtain ⟨χ, χ', h1, h2, h3⟩ := h
      rw [LdRefL.segs]
      exact (LdSegs.fmt_snoc _ _ _ _).2
        ⟨χ, ih χ h1, ldReqRefK_fmt E Kc E0 Rc Pw _ _ _ (S.K.seg S.l S.Qc) S.entry rfl χ χ' ψ h2 h3⟩

theorem ldReqRefK_asSub : Spec.ldReqRefK_asSub := by
  intro E Kc _ _ E0 Rc Pw a b p φ
  induction p with
  | nil => intro ψ h; rw [LdProg.asSub_nil]; exact h
  | snoc p m ih =>
      intro ψ h
      obtain ⟨χ, h1, h2⟩ := (LdProg.fmt_snoc p m φ ψ).1 h
      rw [LdProg.asSub_snoc]
      exact (LdProg.fmt_snoc _ _ _ _).2 ⟨χ, ih χ h1, h2⟩

theorem ldReqRefK_reqFmt : Spec.ldReqRefK_reqFmt := by
  intro F E Kc _ _ _ _ _ R a first a₁ more hm b L T q φ φ₀ φ₁ φb χ χ' h1 h2 h3 h4 h5 h6
  refine ldFmt_req E Kc _ _ _ _ _ (ldReqRef R first a₁ more hm b L T) φ _
    ⟨φ₀, φ₁, φb, h1, h2, ldReqRefK_segsFmt E Kc _ _ _ _ _ _ L φ₁ φb h3, ?_⟩
  refine ldReqRefK_asSub E Kc _ _ _ _ _ (T.tail.app R.lastP) φb _
    (ldProg_app_fmt E Kc _ _ _ _ _ _ _ _ φb _ _ ?_ (ldOREFmt_last F E Kc R q))
  unfold LdRefT.tail
  exact (LdProg.fmt_snoc _ _ _ _).2
    ⟨χ', ldProg_app_fmt E Kc _ _ _ _ _ _ _ _ φb χ χ'
        ((LdProg.fmt_snoc _ _ _ _).2 ⟨φb, (LdProg.fmt_nil _ _ _).2 rfl, h4⟩) h5,
      h6⟩

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem LdProg.asSub_below {a b : LdStage E Kc} (p : LdProg a b) (κ : ℝ≥0∞) :
    p.Below κ → p.asSub.Below κ := by
  induction p with
  | nil => intro h; rw [LdProg.asSub_nil]; exact h
  | snoc p m ih =>
      intro h
      rw [LdProg.asSub_snoc]
      exact (LdProg.below_snoc _ _ _).2
        ⟨ih ((LdProg.below_snoc p m κ).1 h).1, ((LdProg.below_snoc p m κ).1 h).2⟩

theorem LdProg.below_nil (a : LdStage E Kc) (κ : ℝ≥0∞) : (LdProg.nil a).Below κ := by
  rw [LdProg.Below]; trivial

end

theorem ldReqRefK_reqBelow : Spec.ldReqRefK_reqBelow := by
  intro F E Kc _ _ _ _ _ R a first a₁ more hm b L T κ h1 h2 h3 h4 h5
  refine ⟨h1, h2, (ldReqRefK_segs E Kc _ _ _ L).2 κ h3,
    LdProg.asSub_below _ κ (LdProg.below_app _ _ κ ?_ ?_)⟩
  · unfold LdRefT.tail
    exact (LdProg.below_snoc _ _ _).2
      ⟨LdProg.below_app _ _ κ
          ((LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 trivial⟩) h4,
        (errBelow_one _ κ).2 trivial⟩
  · unfold LdORE.lastP
    exact (LdProg.below_snoc _ _ _).2
      ⟨(LdProg.below_snoc _ _ _).2
          ⟨(LdProg.below_snoc _ _ _).2 ⟨LdProg.below_nil _ κ, (errBelow_one _ κ).2 trivial⟩,
            (errBelow_one _ κ).2 h5⟩,
        (errBelow_one _ κ).2 trivial⟩

theorem ldReqRefK_req : Spec.ldReqRefK_req := by
  intro F E Kc _ _ _ _ _ pp _ R a first a₁ more hm b L T hT hn hZ hTie hO hL hB hF
  refine ldOREAt_zk F E Kc R a first a₁ more hm b L.segs T.tail (ldReqRef_tail F E Kc pp R b T hT)
    hn hZ hTie hO ((ldReqRefK_segs E Kc _ _ _ L).1 _ hL) ?_ hF
  unfold LdRefT.tail
  refine (LdProg.zk_snoc _ _ _).2
    ⟨(ldProg_app_zk E Kc _ _ _ _ _ _).2
        ⟨(LdProg.zk_snoc _ _ _).2 ⟨(LdProg.zk_nil _ _).2 trivial, trivial⟩, ?_⟩,
      trivial⟩
  rw [LdProg.after_snoc, LdProg.after_nil]
  exact hB

end Cb
