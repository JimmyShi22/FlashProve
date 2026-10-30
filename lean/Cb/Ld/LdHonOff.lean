-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`Gl.AgreeJ` (Cb/Gl/GlFinalAg.lean) is stated nowhere in this library as a separate theorem: it
follows, by one application that is written down nowhere, from `Cb.BCHKS46At` (`Cb.Gl.glAg_ofAt`,
same file), which this library proves in Cb/Bridge (bchks46At), from files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15), and applies in second
forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file does not apply that proof. Within
half the distance its conclusion is proved (`Cb.Gl.agreeHalf`, Cb/Gl/GlAgreeHalf.lean).






Where a comment below says "the fact
on agreement", `Gl.AgreeJ` is meant.
Cb/Ld/LdHonOff.lean: the part of the object's hypotheses that names neither the request nor the
session's tests (except in the fields `rest0`, `sndOK`, `pl` of this file's records, `lay`, `fitsB`,
`foldB`, `pyInjB`, `monoB` of `HypRestH` and `sndIs`, `sOn`, `own₀` of `CoreH`) is carried from the
premises of `Spec.ldHonRp_off`, at the report's plan, up to the object with the parts' terms
(`T.HypOff L`, Cb/Ld/LdHonObj.lean).

Four records, statements (in `Cb.Spec`) and proofs. Generic: any finite fields F, Fp and any finite
field E that is an algebra over both. Nothing assumed beyond the hypotheses of the statements and
whatever the arguments hold as proofs.
`T.HypOff L` has hypotheses on three sub-protocols: weights-formedness, the offline test and the
link, with the senders and the closings of the last two.

Why: the proof by way of `ldObjRp_hyp`
(Cb/Obj/LdObjectPpRows.lean), `ldObjPp_parts`, `ldObjPp_hyp` (Cb/Obj/LdObjectPlanPaper.lean) and
`ldObjPpCoreP` (Cb/Obj/LdObjectPpCoreP.lean) carries one record at each level, in which "the
request's pack is good" and "each of the session's four whole tests is in order" are beside the
clauses on weights-formedness, the offline test and the link. The two are had under a fact on
agreement of codes alone.
Here the others are carried by themselves.
Each record's clauses are clauses of the record that it is cut from (but rest0, which is typed at
the smaller record; `P.HypOffP` also takes in the four offline clauses of `LdObjPp.Hyp`).

Main names:
  `D.HypRestH L`: `LdObjD.HypRest L` (Cb/Obj/LdObjectTerms.lean) less rHyp, rZk, rFmt, rEnd. It
    keeps the four clauses on the test at N instances (fitsB, foldB, pyInjB, monoB).
  `D.CoreH Zw Y δ p V`: `LdObjD.CoreP` less reqIs, req: no request occurs.
  `Spec.ldHonD_core`: `D.CoreH Zw Y δ p V` ⇒ `D.HypRestH 1` ∧ `Y.Hyp`, for E of characteristic p.
  `P.HypOffP L`, `R.HypOffR L`: the offline halves of `LdObjPp.Hyp L` (with `HypR`),
    `LdObjRp.Hyp L`; `R.HypOffR` holds `R.HypPl` whole: conditions on places, numbers and forms.
  `Spec.ldHonP_off`: `P.HypOffP L` ⇒ `P.toT.HypOff L`.
  `Spec.ldHonRp_off`: `R.HypOffR L` ⇒ `R.toPp.HypOffP L`.



  `Spec.ldHonD_ofRest`, `Spec.ldHonD_ofCore`, `Spec.ldHonP_ofHyp`, `Spec.ldHonRp_ofHyp`:
    `LdObjD.HypRest`, `LdObjD.CoreP`, `LdObjPp.Hyp`, `LdObjRp.Hyp` give these records: nothing new
    is asked.

Limits: this file says nothing on the request, on the test at N instances, on a session, but for the
clauses on these that its records keep (among them fitsB, foldB, pyInjB, monoB; sOn, own₀;
`R.HypPl`; the field `on` of `Y.Hyp`) and
the premises of `Spec.ldHonD_ofRest`, `Spec.ldHonD_ofCore`,
`Spec.ldHonP_ofHyp`, `Spec.ldHonRp_ofHyp`. It does not say that the records hold of any object.



Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdHonObj
import Cb.Gl.GlFinalPpP

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The blocks' own hypotheses, part by part, without those on closings, on the senders
(`LdObjD.HypSnd`, Cb/Obj/LdObjectTerms.lean) and on the request. -/
structure LdObjD.HypRestH (T : LdObjD F E) (L : ℕ) : Prop where
  conf   : T.W.Cf.OK L
  lay    : T.LayOK
  tie    : T.W.Tie
  wfLaws : T.W.P.Laws
  wfHyp  : T.Bw.Hyp
  wfBud  : ∀ l, l ≤ T.W.P.n → ∀ ρ, (T.Bw.sub l).P.bud ρ ∅
  wfNeed : ∀ l, l ≤ T.W.P.n → ∀ ρ U, (T.Bw.sub l).R.need ρ U = U
  q₀e    : T.q₀ ∅
  fold   : T.W.O.toC.P.FoldErr T.W.O.on0 T.εf
  pyInj  : Function.Injective T.W.O.py
  fitsK  : T.K.FitsK T.on0K T.on1K
  foldK  : T.K.P.FoldErr T.on0K T.on1K T.ε₀ T.ε₁
  plInj  : Function.Injective T.K.pl
  bearK  : ∀ a, T.Kc.t ≤ T.Sl.t a
  fitsB  : T.on.ol.Fits T.onB
  foldB  : T.on.ol.toC.P.FoldErr T.onB T.εfB
  pyInjB : Function.Injective T.on.ol.py
  monoB  : ∀ U V, V ⊆ U → T.qaB U → T.qaB V

/-- The clauses that know no plan and no request. -/
structure LdObjD.CoreH (D : LdObjD F E) (Zw : LdWfE F E)
    [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS) (δ : D.Dst Zw) (p : ℕ) {Fp : Type}
    [Field Fp] [Fintype Fp] [Algebra Fp E] (V : Zw.StdW Fp) : Prop where
  wfIs   : (⟨D.W, D.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Zw.W, Zw.G.B⟩
  sndIs  : D = D.std Y
  wfJ    : V.HypJ p δ.dS
  sOff   : Y.TS.NearS Y.LW Y.LU Y.LO Y.tW Y.tU Y.tO δ.dW δ.dU δ.dO
  sLink  : D.K.P.StdNear Y.SdK Y.LK Y.tK Y.YK Y.ixK δ.dN
  sOn    : Y.TB.NearS Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB δ.dWB δ.dUB δ.dOB
  own₀   : D.Own3₀

/-- The offline half of `LdObjPp.Hyp L`. -/
structure LdObjPp.HypOffP (P : LdObjPp F E) (L : ℕ) : Prop where
  rest0  : P.D.HypRestH L
  sndOK  : P.Y.Hyp
  plain  : P.p.Plain
  kept   : P.p.Kept
  rest   : ∀ sa m, P.p.restG.val sa (P.p.Gc.msg (P.p.left₂ m)) = P.W.O.toC.rest sa (P.W.O.toC.aM m)
  saysA  : P.p.SaysA P.TP.Q'.base P.TP.fa
  left   : P.TP.Q'.OK
  leftQ  : ∀ V, P.TP.Q'.q V → P.p.S₃.qFam P.q₀ P.b' V
  kIs    : (⟨P.p.k₀.o, P.p.k₀.j⟩ : P.W.O.toC.S.Ent) = P.W.O.toC.eO (P.Y.TS.YO.entF P.n₀)
  noPad  : ∀ n, P.p.Rs₀ (P.W.O.toC.eO n) → P.Y.TS.YO.NoPad n
  needA  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inl (.inl (.inl a))) ≤ P.Bw.t a
  needW  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inl (.inl (.inr a))) ≤ P.Y.tW a
  needU  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inl (.inr a)) ≤ P.Y.tU a
  needO  : ∀ a, P.TP.D₁.need (P.TP.D₂.need (P.TP.D₃.need P.b')) (.inr a) ≤ P.Y.tO a
  close  : P.Kc.OK
  test₁  : P.TP.D₁.OK
  test₂  : P.TP.D₂.OK
  test₃  : P.TP.D₃.OK

/-- The offline half of `LdObjRp.Hyp L`. -/
structure LdObjRp.HypOffR (R : LdObjRp F E) (L : ℕ) : Prop where
  rest0  : (R.toLdObjD.std R.Y).HypRestH L
  sndOK  : R.Y.Hyp
  pl     : R.HypPl
  close  : R.Kc.OK
  test₁  : R.TP₀.D₁.OK
  test₂  : R.TP₀.D₂.OK
  test₃  : R.TP₀.D₃.OK
  test₄  : R.X.run.OK

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldHonD_ofRest : Prop := ∀ (D : LdObjD F E) (L : ℕ), D.HypRest L → D.HypRestH L

def ldHonD_ofCore : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (p : ℕ) (D : LdObjD F E)
      (Zw : LdWfE F E) [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS) (δ : D.Dst Zw)
      (P : LdReqPack F E) (V : Zw.StdW Fp),
    D.CoreP Zw Y δ p P V → D.CoreH Zw Y δ p V

def ldHonP_ofHyp : Prop := ∀ (P : LdObjPp F E) (L : ℕ), P.Hyp L → P.HypOffP L

def ldHonRp_ofHyp : Prop := ∀ (R : LdObjRp F E) (L : ℕ), R.Hyp L → R.HypOffR L

def ldHonD_core : Prop :=
  ∀ (Fp : Type) [Field Fp] [Fintype Fp] [Algebra Fp E] (p : ℕ) [CharP E p]
      (D : LdObjD F E) (Zw : LdWfE F E) [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS)
      (δ : D.Dst Zw) (V : Zw.StdW Fp),
    D.CoreH Zw Y δ p V → D.HypRestH 1 ∧ Y.Hyp

def ldHonP_off : Prop := ∀ (P : LdObjPp F E) (L : ℕ), P.HypOffP L → P.toT.HypOff L

def ldHonRp_off : Prop := ∀ (R : LdObjRp F E) (L : ℕ), R.HypOffR L → R.toPp.HypOffP L

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldHonD_ofRest : Spec.ldHonD_ofRest F E := fun _ _ h =>
  { conf := h.conf, lay := h.lay, tie := h.tie, wfLaws := h.wfLaws, wfHyp := h.wfHyp,
    wfBud := h.wfBud, wfNeed := h.wfNeed, q₀e := h.q₀e, fold := h.fold, pyInj := h.pyInj
    fitsK := h.fitsK, foldK := h.foldK, plInj := h.plInj, bearK := h.bearK, fitsB := h.fitsB,
      foldB := h.foldB, pyInjB := h.pyInjB, monoB := h.monoB }

theorem ldHonD_ofCore : Spec.ldHonD_ofCore F E := fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, wfJ := h.wfJ, sOff := h.sOff, sLink := h.sLink,
    sOn := h.sOn, own₀ := h.own₀ }

theorem ldHonP_ofHyp : Spec.ldHonP_ofHyp F E := fun P L h =>
  { rest0 := ldHonD_ofRest F E P.D L h.r.rest0, sndOK := h.r.sndOK, plain := h.r.plain,
    kept := h.r.kept, rest := h.r.rest, saysA := h.r.saysA, left := h.r.left, leftQ := h.r.leftQ,
    kIs := h.r.kIs, noPad := h.r.noPad
    needA := h.r.needA, needW := h.r.needW, needU := h.r.needU, needO := h.r.needO,
      close := h.close, test₁ := h.test₁, test₂ := h.test₂, test₃ := h.test₃ }

theorem ldHonRp_ofHyp : Spec.ldHonRp_ofHyp F E := fun _ L h =>
  { rest0 := ldHonD_ofRest F E _ L h.rest0, sndOK := h.sndOK, pl := h.pl, close := h.close,
    test₁ := h.test₁, test₂ := h.test₂, test₃ := h.test₃, test₄ := h.test₄ }

theorem ldHonD_core : Spec.ldHonD_core F E := by
  intro Fp _ _ _ p _ D Zw _ Y δ V h
  have hC : D.W.Cf.Third := by
    have key : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Zw.W, Zw.G.B⟩ → x.1.Cf.Third := by
      rintro _ rfl
      exact h.wfJ.conf3
    exact key ⟨D.W, D.Bw⟩ h.wfIs
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ :=
    ldObjZ_wf p Zw 1 (ldWfE_okStd F E Fp Zw V p 1 (ldObjRefJ_wf F E Fp Zw V p δ.dS h.wfJ))
      ⟨D.W, D.Bw⟩ h.wfIs
  have own := ldObjRefJ_own F E D h.own₀ hC
  exact
    ⟨{ conf := w1, lay := own.lay, tie := w2, wfLaws := w3, wfHyp := w4, wfBud := w5, wfNeed := w6,
       q₀e := own.q₀e, fold := own.fold, pyInj := own.pyInj
       fitsK := own.fitsK, foldK := own.foldK, plInj := own.plInj, bearK := own.bearK
       fitsB := own.fitsB, foldB := own.foldB, pyInjB := own.pyInjB, monoB := own.monoB },
     ⟨ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOff,
       ldObjRefJ_link _ E _ _ _ _ _ _ _ _ _ _ _ h.sLink,
       ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOn⟩⟩

open Classical in
theorem ldHonP_off : Spec.ldHonP_off F E := by
  intro P L h
  classical
  have hS := ldObjS_snd P.toLdObjD P.Y h.sndOK
  have hr := h.rest0
  have hSaysO : P.W.O.toC.Says (P.p.x₁ P.TP.Q'.base).A (P.W.O.toC.fqP P.TP.fa) :=
    ldLinPp_says E _ _ _ _ P.W.O.toC P.p _ P.TP.Q'.base P.TP.fa h.rest h.saysA
  have o0 : P.p.Rs₀ (P.W.O.toC.eO (P.Y.TS.YO.entF P.n₀)) := h.kIs ▸ h.plain.rs₀K
  have ol := stdL_ownOne P.Y.Fp E P.W.O.toC.P.NO P.Y.TS.YO P.Y.tO P.W.O.toC.P.W4 P.W.O.toC.P.W3
    P.Y.TS.datO (fun w => w.2) (fun _ => 0, P.Y.TS.w3) P.n₀ P.W.O.toC.P.SdO
    (fun n => P.p.Rs₀ (P.W.O.toC.eO n)) h.sndOK.off.okO h.noPad o0
  have of0 := ldLinSp_entO E _ _ _ _ P.W.O.toC P.W.O.on0 P.εf P.D.Sn (P.p.x₁ P.TP.Q'.base)
    (P.W.O.toC.fqP P.TP.fa)
    (P.Y.TS.YO.ownOne P.Y.TS.datO (fun w => w.2) (fun _ => 0, P.Y.TS.w3) P.n₀) P.p.Rs₀
    (fun _ => False) (P.Y.TS.YO.entF P.n₀) ol hS.snd.hidO (fun _ h => h) o0
  rw [← h.kIs] at of0
  have hbehO := ldLinPpT_behindA E _ _ _ _ P.W.O.toC P.p P.TP P.W.O.on0 P.εf P.D.Sn P.p.Rs₀
    (fun _ => False) hr.fold hr.pyInj hS.snd h.rest h.saysA h.plain h.kept h.test₁ h.test₂ h.test₃
    h.left (fun _ h => h) of0
  have hdemO := ldLinPpT_demand E _ _ _ _ P.W.O.toC P.p P.TP P.D.Sn
    (P.W.O.S.qFam (E₀ := extNone) P.q₀ P.Bw.t) P.q₀ P.Bw.t P.b' h.leftQ (fun _ hW => hW)
    h.needA h.needW h.needU h.needO
  exact
    { conf := hr.conf, tie := hr.tie, wfLaws := hr.wfLaws, wfHyp := hr.wfHyp, wfBud := hr.wfBud,
      wfNeed := hr.wfNeed, q₀e := hr.q₀e, fold := hr.fold, pyInj := hr.pyInj
      fitsK := hr.fitsK, foldK := hr.foldK, plInj := hr.plInj, bearK := hr.bearK, snd := hS.snd,
        sndK := hS.sndK, close := h.close, rows := hSaysO, plan := hbehO, demand := hdemO }

theorem ldHonRp_off : Spec.ldHonRp_off F E := by
  intro R L h
  obtain ⟨a1, a2, a3⟩ :=
    ldOWfRowsP_three F E R.W R.nAt R.p R.X R.wX h.pl.entAt h.pl.nowX h.pl.kpX h.pl.plR h.test₄
  exact
    { rest0 := h.rest0
      sndOK := h.sndOK
      plain := h.pl.plain
      kept := h.pl.kept
      rest := ldOWfRestP_is F E R.W R.nAt R.p h.pl.entAt h.pl.restIs h.pl.plW h.pl.plC
      saysA := a1
      left := a2
      leftQ := by
        intro V hV
        have := a3 V hV
        show R.p.S₃.qFam R.q₀ _ V
        rw [h.pl.q₀is]
        exact this
      kIs := h.pl.kIs
      noPad := h.pl.noPad
      needA := h.pl.needA
      needW := h.pl.needW
      needU := h.pl.needU
      needO := h.pl.needO
      close := h.close
      test₁ := h.test₁
      test₂ := h.test₂
      test₃ := h.test₃ }

end
end Cb
