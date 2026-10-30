-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadFit.lean: what the statements on the forms of the output head's lookup calls ask,
as conclusions from the verifier's own functions.

Johnson/Road/HeadCallLib.lean says what the form of a lookup call's key vector is worth, under one
record of hypotheses (LinesFit) and some hypotheses on the call (its point, its segments' names).
This file derives them from what the verifier's own functions return, at the library's sizes:
 - the function layout returns a layout (Johnson/Road/HeadLaid.lean);
 - the routine hear has returned what was heard, in the form of the record HeardFits
   (Johnson/Road/HeadPoint.lean);
 - the reads are true of cells, in the form of the record TrueH (Johnson/Road/HeadReads.lean shows
   it of the tables that the routine tablesOf returns, if every read holds);
 - the request is the library's (ReqFits; Johnson/Road/HeadLaid.lean shows it of an instance).

The point. All calls' key points end in the same coordinates, x.Zl: its first ls coordinates belong
to the entries of a block, the others to the positions.

Main theorems: linesFit_of_run; point_of_run; costTables_of_run (two more tables, which the claims
on the costs read); reqOf_ok. Johnson/Road/HeadLinkRun.lean, HeadLinkPort.lean
and HeadLinkLPort.lean read them.

What is not claimed. That the reads hold, that the routines succeed and that the shape has the
numbers named in the hypotheses is not shown. Nothing is said about what a verifier's acceptance
shows. The program does not import this file.
-/
import Johnson.Road.HeadCallLib
import Johnson.Road.HeadPoint
import Johnson.Road.HeadMet

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading World Aff Fork SubM)

variable {K : Type} [Field K]

/-- A segment with the public half of the record SegFit has a call. -/
theorem SegLaid.call {R : Model.Head.Run} {sn : String} {n : ℕ} (S : SegLaid R sn n) :
    ∃ q, Model.Head.callNo R.L sn = some q := by
  obtain ⟨q, _, hq, _⟩ := S
  exact ⟨q, hq⟩

/-- Every checked token of an instance is a token. -/
theorem reqOf_ok (x : Inst.Model.Instance Inst.Model.ppref) : (Cm.reqOf x).OK :=
  fun i => x.w_lt i

/-- **The record LinesFit, from the verifier's own functions**, at the library's sizes. hy: the
layout is what the function layout returns. Xh: what was heard has passed the tests of the routine
hear. T: the reads are true of the cells t. Y, hOK: the request y is the run's, and its checked
tokens are tokens. The five numbers are public. -/
theorem linesFit_of_run {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    {cov : Model.Head.Covered} {x : Model.Head.Heard}
    (hy : Model.Head.layout h tauFC = .ok L) (Xh : HeardFits h L cov x) (ρ : Reading K)
    {W : World K} {R : Model.Head.Run} (e1 : R.h = h) (e2 : R.L = L) (e3 : R.x = x)
    (h1 : h.lt = 10) (h2 : h.d = 5120) (h3 : h.V = 202048) (hsh : h.digSh = 8) (hXL : h.XL = 5)
    {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) (hOK : y.OK) {K3 : ℕ}
    {t : Inst.Model.Head.Cells K} (T : TrueH ρ W R K3 t) :
    LinesFit ρ W R HeadSizes.ref K3 t y (pt ρ R.x.Zl) (fun j => pt ρ R.x.Zl (R.h.ls + j)) := by
  subst e1 e2 e3
  have Z : Laid R HeadSizes.ref := laid_ref hy h1 h2 h3 rfl rfl
  obtain ⟨sNF, sNFH, sCNF, sHD0, sHD1, sHD2, sHE0, sHE1⟩ := eight_of_layout hy (R := R) rfl rfl
  have sROW := row_of_layout hy (R := R) rfl rfl
  rw [Z.d] at sNF sNFH sCNF
  rw [Z.JV] at sHD0 sHD1 sHD2
  rw [Z.JVa] at sHE0
  rw [Z.JV, Z.JVa] at sHE1
  rw [hXL] at sROW
  have hls : R.h.ls ≤ 17 := by
    by_contra hc
    have a : 2 ^ 11 ∣ 2 ^ R.h.ls := Nat.pow_dvd_pow 2 (by omega)
    have b : 2 ^ 11 ∣ 5120 := Nat.dvd_trans a Z.Sd
    exact absurd b (by decide)
  have pos : ∀ {sn : String} {n : ℕ}, SegLaid R sn n →
      PosFit ρ R sn (fun j => pt ρ R.x.Zl (R.h.ls + j)) := by
    intro sn n S
    obtain ⟨q, hq⟩ := S.call
    exact posFit_of_run hy Xh ρ rfl rfl rfl hq
  have fit : ∀ {sn : String} {n : ℕ}, SegLaid R sn n → SegFit ρ R sn n (pt ρ R.x.Zl) :=
    fun S => segFit_of_run hy Xh ρ rfl rfl rfl S
  exact {
    laid := Z
    req := Y
    sh := hsh
    XL := hXL
    qH := Xh.qH
    win := fun i _ _ => hOK i
    Sa := Nat.pow_dvd_pow 2 hls
    Va := by decide
    long := longAt_of_sum (Zl_parts hy Xh) T.hfZ
    hd := by
      obtain ⟨q, hq⟩ := sCNF.call
      have P := point_of_call hy Xh ρ (callNo_lt hq)
      exact ShortAt.congr P.2.2.2 (shortAt_of_sum P.2.2.1 (T.hdFC q hq))
    hr := by
      obtain ⟨q, _, hq, _⟩ := sROW
      have P := point_of_call hy Xh ρ (callNo_lt hq)
      exact ShortAt.congr P.2.2.2 (shortAt_of_sum P.2.2.1 (T.hrROW q hq))
    phiC := by
      have P := point_of_call hy Xh ρ (callNo_lt Xh.qH)
      exact ShortAt.congr P.2.2.2 (shortAt_masked P.2.2.1
        (fun i => ((HeadSizes.rhoC HeadSizes.ref y i : ℤ) : K)) (Y.rhoCK Z) T.hrPhiC)
    sNF := fit sNF
    sNFH := fit sNFH
    sHD0 := fit sHD0
    sHD1 := fit sHD1
    sROW := sROW
    sHD2 := fit sHD2
    sHE0 := fit sHE0
    sHE1 := fit sHE1
    sCNF := fit sCNF
    uHD0 := pos sHD0
    uHD1 := pos sHD1
    uHD2 := pos sHD2
    uHE0 := pos sHE0
    uHE1 := pos sHE1 }

/-- **The point of a call**, as Johnson/Road/HeadCallLib.lean asks for it: the call's key point,
read by ρ, has the column coordinates first, and then the position coordinates that all calls
share. -/
theorem point_of_run {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    {cov : Model.Head.Covered} {x : Model.Head.Heard}
    (hy : Model.Head.layout h tauFC = .ok L) (Xh : HeardFits h L cov x) (ρ : Reading K)
    {R : Model.Head.Run} (e1 : R.h = h) (e2 : R.L = L) (e3 : R.x = x) {q : ℕ}
    (hq : q < R.L.calls.size) :
    (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ ∧
      (∀ k, k < (R.L.calls.getD q default).lJ →
        pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = pt ρ (R.x.g1.zk.getD q #[]) k) ∧
      ∀ k, k < R.h.lt → pt ρ (R.x.g1.zk.getD q #[]) ((R.L.calls.getD q default).lJ + k) =
        pt ρ R.x.Zl (R.h.ls + k) := by
  subst e1 e2 e3
  have P := point_of_call hy Xh ρ hq
  have zs := (zk_size hy Xh hq).2
  refine ⟨P.1, fun k hk => ?_, fun k hk => ?_⟩
  · show ρ.val (((R.x.g1.zk.getD q #[]).extract 0 (R.L.calls.getD q default).lJ).getD k zeroE) =
      ρ.val ((R.x.g1.zk.getD q #[]).getD k zeroE)
    rw [getD_extract _ (by omega) (by omega), Nat.zero_add]
  · rw [← P.2.2.2 k hk]
    show ρ.val ((R.x.g1.zk.getD q #[]).getD ((R.L.calls.getD q default).lJ + k) zeroE) =
      ρ.val (((R.x.g1.zk.getD q #[]).extract (R.L.calls.getD q default).lJ
        ((R.L.calls.getD q default).lJ + R.h.lt)).getD k zeroE)
    rw [getD_extract _ (by omega) (by omega)]

/-! ## The tables on the costs -/

/-- **The two tables that the claims on the costs read beside "hr@phiC"**, true of the cells: the
plain sums of the ledger's cells over the counted positions, and the cells of hf at the counted
positions, with the weight 1 on each feature of a block, at the positions' point. -/
theorem costTables_of_run {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    {cov : Model.Head.Covered} {x : Model.Head.Heard}
    (hy : Model.Head.layout h tauFC = .ok L) (Xh : HeardFits h L cov x) (ρ : Reading K)
    {W : World K} {R : Model.Head.Run} (e1 : R.h = h) (e2 : R.L = L) (e3 : R.x = x)
    (Z : Laid R HeadSizes.ref) {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) {K3 : ℕ}
    {t : Inst.Model.Head.Cells K} (T : TrueH ρ W R K3 t) :
    SumAt W R K3 "hr@rhoC" Inst.Model.Head.nT (fun φ a => ((y.rhoC a : ℤ) : K) * t.hr φ a) ∧
      FlatAt W R K3 "hf@phiZ" R.h.ls R.h.lt (fun j => pt ρ R.x.Zl (R.h.ls + j))
        (fun φ a => ((y.rhoC a : ℤ) : K) * t.hf φ a) := by
  subst e1 e2 e3
  have P := point_of_call hy Xh ρ (callNo_lt Xh.qH)
  have hla : R.h.la = R.h.ls + R.h.lt := (Zl_size Xh).symm.trans (Zl_parts hy Xh)
  have hT : 2 ^ R.h.lt = Inst.Model.Head.nT := Z.T.symm
  have s1 := sumAt_masked P.2.2.1 (fun i => ((HeadSizes.rhoC HeadSizes.ref y i : ℤ) : K))
    (Y.rhoCK Z) T.hrRhoC
  rw [hT] at s1
  exact ⟨s1, FlatAt.congr P.2.2.2 (flatAt_masked P.2.2.1 hla
    (fun i => ((HeadSizes.rhoC HeadSizes.ref y i : ℤ) : K)) (Y.rhoCK Z) T.hfPhiZ)⟩

#print axioms linesFit_of_run
#print axioms point_of_run
#print axioms reqOf_ok
#print axioms costTables_of_run

end OnBytes.Road.Hd
