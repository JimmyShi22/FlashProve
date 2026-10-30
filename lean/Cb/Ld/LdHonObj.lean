-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/Ld/LdHonObj.lean: the honest half of the object with the parts' terms
(`T : LdObjT`,
Cb/Obj/LdObjectTerms.lean), clause by clause. The four clauses wf, linOff, link, fitOff of
`Hiop.SubsR.HypH` follow from a part of `T.Hyp L` that names neither the request nor the closing of
the test at N instances; then comes the assembly of all seven.

One record, statements (in `Cb.Spec`) and proofs. Generic: a variable T. Nothing assumed beyond the
hypotheses of the statements and whatever the arguments hold as proofs. The honest half is
`SubsR.HypH` (Hiop/RecBuild.lean): the parameter lists of the sub-protocols (wf, linOff, link, req,
linOn) without their items on knowledge soundness, which are in `SubsR.HypK`, and the two clauses
fitOff, fitOn.

Why: `Cb.ldObjT_hyp` takes `T.Hyp L` whole and gives `S.Hyp P` whole. Where the request's and the
session's clauses of `T.Hyp L` are had only under an assumed statement on codes, so is all of
`S.Hyp P`, the offline phase's and the link's honest items too. The proofs of `Cb.ldObjT_ok` and
`Cb.ldObj_hyp` go clause by clause: here the clauses are taken apart.

Main names:
  `T.HypOff L`: nineteen clauses of `T.Hyp L`, word for word (its fields: see the record). Beside
    the request's four clauses and the closing's six it leaves out lay, fitsB, foldB, pyInjB, monoB,
    sndB, apartB.
  `Spec.ldHonT_ofHyp`: `T.Hyp L` → `T.HypOff L`: the record is a part of `T.Hyp L`.
  `Spec.ldHonT_hypH`: `T.HypOff L` → the clause req → the clause linOn → the clause fitOn →
    `T.obj.subs.HypH T.obj.nums`.

Limits: this file does not say that `T.HypOff L` or one of the three clauses holds anywhere. It says
nothing on knowledge soundness of the object. This file says nothing on the value of any number.
An assembly. `T.HypOff L` still holds knowledge soundness of the offline phase and of the link at
their true errors (wfHyp, plan, close are bundles with both sides): it is no honest half of these.







Terms: lean/GLOSSARY.md.

-/
import Cb.Obj.LdObjectTermsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

open Classical in
/-- A part of `T.Hyp L` that names neither the request nor the closing of the test at N instances.
-/
structure LdObjT.HypOff {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (T : LdObjT F E) (L : ℕ) : Prop where
  conf   : T.W.Cf.OK L
  /-- weights-formedness -/
  tie    : T.W.Tie
  wfLaws : T.W.P.Laws
  wfHyp  : T.Bw.Hyp
  wfBud  : ∀ l, l ≤ T.W.P.n → ∀ ρ, (T.Bw.sub l).P.bud ρ ∅
  wfNeed : ∀ l, l ≤ T.W.P.n → ∀ ρ U, (T.Bw.sub l).R.need ρ U = U
  /-- the offline test -/
  q₀e    : T.q₀ ∅
  fold   : T.W.O.toC.P.FoldErr T.W.O.on0 T.εf
  pyInj  : Function.Injective T.W.O.py
  /-- the link -/
  fitsK  : T.K.FitsK T.on0K T.on1K
  foldK  : T.K.P.FoldErr T.on0K T.on1K T.ε₀ T.ε₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  /-- the senders of the offline test and of the link -/
  snd    : T.Sn.OK
  sndK   : T.Sl.OK
  /-- the closings of the link and of the offline test -/
  close  : T.Kc.OK
  rows   : T.W.O.toC.Says T.Qt.base T.fq
  plan   : T.Qt.OkBehind
    ((T.W.O.toC.P.chain T.W.O.on0 T.Sn T.εf).append (T.W.O.toC.chain T.fq T.Qt.base))
  demand : ∀ V, T.Qt.q V →
    T.W.O.toC.P.q5 T.Sn (T.W.O.S.qFam (E₀ := extNone) T.q₀ T.Bw.t) (V.biUnion T.W.O.toC.toE.src)

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldHonT_ofHyp : Prop := ∀ (T : LdObjT F E) (L : ℕ), T.Hyp L → T.HypOff L

open Classical in
/-- States: `T.HypOff L` and the three clauses req, linOn, fitOn give the seven clauses,
`T.obj.subs.HypH T.obj.nums`. -/
def ldHonT_hypH : Prop :=
  ∀ (T : LdObjT F E) (L : ℕ), T.HypOff L →
    PreListR T.obj.subs.on T.obj.subs.req T.obj.subs.hReq Prod.snd Prod.fst
      T.obj.Cf.conf.Rreq T.obj.nums.req →
    LinBListR T.obj.subs.on T.obj.subs.linOn T.obj.subs.hLinOn T.obj.subs.N T.obj.nums.linOn →
    (∀ ρ₁ ρ₂,
      T.obj.nums.req.bud ρ₁ ((T.obj.subs.linOn.ior.extReads ρ₂).biUnion (T.obj.subs.req.srcO ρ₁))) →
    T.obj.subs.HypH T.obj.nums

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldHonT_ofHyp : Spec.ldHonT_ofHyp F E := fun _ _ h =>
  { conf := h.base.rest.conf, tie := h.base.rest.tie, wfLaws := h.base.rest.wfLaws,
    wfHyp := h.base.rest.wfHyp, wfBud := h.base.rest.wfBud, wfNeed := h.base.rest.wfNeed
    q₀e := h.base.rest.q₀e, fold := h.base.rest.fold, pyInj := h.base.rest.pyInj,
      fitsK := h.base.rest.fitsK, foldK := h.base.rest.foldK,
      plInj := h.base.rest.plInj, bearK := h.base.rest.bearK
    snd := h.base.snds.snd, sndK := h.base.snds.sndK, close := h.close, rows := h.rows,
      plan := h.plan, demand := h.demand }

theorem ldHonT_hypH : Spec.ldHonT_hypH F E := by
  classical
  intro T L h hR hB hF
  obtain ⟨f1, f2, f3⟩ := LdWfP.link_all h.wfLaws h.wfHyp
  have hTail := ldOLF_tailFA F E T.W.O T.εf T.Sn T.q₀ T.Bw.t T.Qt T.fq T.dT T.dT₀ h.q₀e h.fold
    h.pyInj h.snd h.rows h.plan h.demand
  have hCl := ldLkC_chain _ _ _ _ _ T.K.P T.Kc T.dK₂ T.Sl _
    (T.K.P.coreC T.on0K T.on1K T.Sl T.ε₀ T.ε₁) h.close h.bearK
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ hTail
  have hwf : T.obj.wf.OK T.obj.cw :=
    { good := LdWfP.link_goodT h.wfLaws h.wfHyp
      prefx := f1
      passes := f2
      hands := f3
      relB := fun x y w hw => ⟨hw.1, (ldOWf_holds T.W h.tie _ _ _ _).1 hw.2⟩
      relRB := fun a m U hU hh => ⟨U, hU, (ldOWf_holds T.W h.tie _ _ _ _).2 hh⟩
      onB := fun _ ha => ha }
  have hlin : T.obj.lin.OK := ⟨hTail, fun U hU => by
    rw [ldOl_card_isLeft]
    exact hU.1⟩
  have hlink : T.obj.K.TailOKAt T.obj.on0K T.obj.on1K T.obj.link :=
    ldLc_tail T.K.P T.on0K T.on1K T.ε₀ T.ε₁ T.Sl (T.Kc.cZ T.dK₂)
      T.dK h.foldK h.plInj h.sndK hCl.1 hCl.2
  have hfit : ∀ ρ₁ ρ₂,
      T.obj.wf.nums.bud ρ₁ ((T.obj.lin.Q.extReads ρ₂).biUnion (T.obj.wf.wf.srcO ρ₁)) := by
    refine ldOWf_fit T.W T.Bw T.linT.Q (fun V => V.card ≤ T.W.O.t) h.wfHyp h.wfBud h.wfNeed
      (fun U V hVU hU => ⟨?_, fun a => ?_⟩) h9
    · exact (Finset.card_le_card (Finset.toLeft_subset_toLeft hVU)).trans hU.1
    · exact (cnt_mono fun x hx => hVU hx).trans (hU.2 a)
  exact
    ⟨(ldOW_object F E T.obj.off.ol T.obj.Kw T.obj.wf T.obj.cw hwf).1,
     (ldOT_object F E T.obj.off.ol T.obj.lin T.obj.dOff h.conf.core.dist h.conf.rad hlin).1,
     (ldOlA_object F E T.obj.Cf T.obj.K T.obj.on0K T.obj.on1K T.obj.link L h.conf h.fitsK hlink).1,
     hR, hB, hfit, hF⟩

end
end Cb
