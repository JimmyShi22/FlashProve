-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerEnds3S.lean: the verifier's claims on the end values of the second token
sumcheck of a layer sub-proof say, on true reads, that each hidden end value is the true contraction
of the cells at the sumcheck's end point.

Main definitions.
 - termsL: the claims of claimsTerms (OnBytes/Model/Layer.lean) as a list of forms, in its order.
 - L3EndShown: if every table of the reads holds what it says of the matrices Mm, and every form of
   termsL is worth 0, then Pub34.EndsL3 (Johnson/Road/Rows/LayerEnds3Y.lean) holds at the cells of
   Mm.
Main theorem: l3EndShown, for every public record.

How. The reciprocal of a norm is a number that the verifier composes from six digits of the norm's
row, read in the short tables of the matrix ar at the end point: row5At_cells
(Johnson/Road/FormsKeysIdnW.lean), Hd.row5_R (Johnson/Road/HeadLedgerLin.lean) and the library's
ext_R. A score and a selector's entry are single entries of short tables: PortFits.shA2
(Johnson/Road/FormsKeysLate.lean).

What is not claimed. Nothing on soundness, and nothing on hiding. That a form of the list is worth 0
is a hypothesis. The program does not read this file.

-/
import Johnson.Road.Rows.LayerEnds3Y
import Johnson.Road.FormsKeysIdnW
import Johnson.Road.FormsKeysClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff CallD Seg WsShape WsClaim HFun HTailF2 Level lastOf wsLayOf
  eqTab)
open OnBytes.Model.Layer (Env Lay Heard Reads TableAsk TableAt PanelEnv ClaimEnv Panels StackEnd
  layout scalesHeld readsOf layTables tableAsks panelsA panelsT placePanels stackEnd pointsOf funsOf
  matIx)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan used led)

variable {K : Type} [Field K]

/-! ## The tables at the end point, from one hypothesis on the reads -/

section Facts

variable {ρ : Reading K} {Wo : World K} {h : Model.Layer.Shape} {pc : List (List String)}
  {p : PanelEnv} {c : ClaimEnv} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {D : Dim} {s : WsShape} {lk : ℕ}
  {tb : Tables} {Zp : Array E} {ends : Array (Array E)} {s0 : Model.Forest.Shape} {H : Heard}
  {tT : Model.Tsc} {tl : HTailF2} {hd : Level} {hd2 : Option Level}
  {pts : List (String × Array E)} {funs : Array HFun}

/-- The record PortFits (Johnson/Road/FormsKeysPort.lean) and the four families of tables at the end
point of the second token sumcheck, under the public hypotheses of capstone
(Johnson/Road/FormsKeysCaller.lean) and its one hypothesis on the reads. -/
theorem port_holds (hy : layout h pc = .ok p.v.y) (S : Switches h)
    (hs : scalesHeld h p.v.sc = .ok ()) (hg : p.v.g < p.v.y.NGr) (hrd : readsOf p.v.y = .ok rd)
    (hl : layTables (matsR p.v.y p.v.g) (tableAsks p.v.y rd p.v.g) 0 = some r)
    (ht : p.v.tab = r.1) (hρ : Numerals ρ) (Z : Sized h D) (hc : D.cap = h.lidb)
    (hN : LinesAre p.v.y) (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k))
    (hsx : H.fo.zx.size = p.v.y.fo.dT) (hsy : H.fo.zy.size = p.v.y.fo.rK)
    (hzk : p.v.zk = (Array.range p.v.y.fo.NC).map fun q =>
      H.fo.zy.extract (p.v.y.fo.rK - p.v.y.fo.iota.getD q 0) H.fo.zy.size ++ H.fo.zx)
    (he : p.e = (Array.range p.v.y.fo.NC).map (Model.Forest.callWeight p.v.y.fo H.fo.zy))
    (hZ : lastOf H.fo.zx p.v.y.h.la = .ok Zp) (hzt : lastOf H.fo.zx p.v.y.h.lt = .ok H.ztF)
    (hm : p.v.zk.mapM (fun z => (lastOf z p.v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Zp) = true)
    (hs0 : Model.Forest.shape p.v.y.cl p.v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (env : p.v = c.v) (Zw : SizedW s D.P) (hsL : s.L = h.L)
    (hlw : wsLayOf s true lk = .ok c.wsLay) (h4 : h.p4 = true) (hcrt : c.rt = tT.r)
    (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb (c.v.g * c.v.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR p.v.y p.v.g) (hNM : tl.NM = tl.mats.size)
    (hpts : pointsOf p.v.y H hd hd2 = some pts)
    (hfun : funsOf p.v.y H.fo pts r.2.1 = some funs) (hT : H.tT = some tT) (Mm : Mats K)
    (Hd : ∀ Fn ∈ funs, Holds ρ Wo tl p.v.iU3 p.v.K3 Mm Fn) :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    PortFits ρ Wo p.v D (cellsAt p.v.y Mm) (cellsOf D (cellsAt p.v.y Mm)) (pt ρ Zp)
        (zOf ρ H.fo.zx H.fo.zy) (pt ρ c.rt) ∧
      TrueAt2 ρ Wo p.v h.lt (cellsAt p.v.y Mm) (pt ρ Zp) (pt ρ c.rt) := by
  letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
  have sh := (admitted_of_layout hy S.p3).shape
  obtain ⟨Z1, hZ1, T⟩ := trueAt_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hzt hfun Mm Hd
  obtain ⟨Z2, hZ2, hr2, T2⟩ :=
    trueAt2_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun hT Mm Hd
  have e1 : Z1 = Zp := Except.ok.inj (hZ1.symm.trans hZ)
  have e2 : Z2 = Zp := Except.ok.inj (hZ2.symm.trans hZ)
  subst e1
  subst e2
  have Ro := shortQa_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun h4 Mm Hd
  rw [sh] at T T2 Ro
  rw [← hcrt] at T2 hr2
  have hrt : c.rt.size = D.lT := by rw [hr2, sh, Z.lT]
  exact ⟨(sigFits_of_look hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt
    env Zw hsL hlw h4 hrt R T T2 Ro).port, T2⟩

end Facts

/-! ## The claims on the end values -/

/-- The claims of claimsTerms (OnBytes/Model/Layer.lean), in its order: for each end value the
hidden value under its slot, less its form in the reads at the end point. sEnd: the slot of the
first end value. Returns none if a form is absent. -/
def termsL (v : Env) (sEnd : ℕ) : Option (List Aff) :=
  appL (((List.range (v.y.NN * v.y.Lam)).mapM fun i =>
      (v.rowR "rt" i).bind fun f => some [Aff.slot (sEnd + i) - f]).map List.flatten)
    (if v.y.h.p3 then
      appL (((List.range v.y.LamM).mapM fun lm =>
          (v.shA "sc" "rt" lm 0).bind fun f =>
            some [Aff.slot (sEnd + v.y.NN * v.y.Lam + lm) - f]).map List.flatten)
        (((List.range (v.y.LamM * v.y.h.NE)).mapM fun x =>
          (v.shA "sel" "rt" (x / v.y.h.NE) (x % v.y.h.NE)).bind fun f =>
            some [Aff.slot (sEnd + v.y.NN * v.y.Lam + v.y.LamM + x) - f]).map List.flatten)
    else some [])

/-- The end of the second token sumcheck on the side of its end values: the verifier's claims on
them, on true reads, say that each hidden end value is the true contraction. -/
def L3EndShown (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (Mm : Mats K) (hh : ℕ → ℕ → K) (l : List Aff),
    X.ReadsTrue Wo Mm → termsL X.p.v X.tT.sEnd = some l → (∀ f ∈ l, f.value X.ρ Wo = 0) →
      X.EndsL3 Wo Mm hh

theorem l3EndShown (X : Pub34 K) : L3EndShown X := by
  intro Wo Mm hh l hRd hl hz
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  obtain ⟨P, T2⟩ := port_holds X.hy X.S X.hs X.hg X.hrd X.hl X.ht X.hρ X.Z X.hc X.hN X.hfl X.hsx
    X.hsy X.hzk X.he X.hZ X.hzt X.hm X.ha X.hs0 X.hpt X.env X.Zw X.hsL X.hlw X.h4 X.hcrt X.R X.htm
    X.hNM X.hpts X.hfun X.hT Mm hRd
  have F := P.fits
  obtain ⟨la, lb, ha, hb, rfl⟩ := appL_some hl
  rw [if_pos F.p3] at hb
  obtain ⟨lc, ld, hc, hd, rfl⟩ := appL_some hb
  unfold Pub34.EndsL3
  refine ⟨fun ν hν => ?_, fun l' hl' => ?_, fun l' e hl' he => ?_⟩
  · have hν' : ν < X.p.v.y.NN * X.p.v.y.Lam := by rw [F.NN, F.Lam]; exact hν
    obtain ⟨x, hx, hin⟩ := mem_flat ha (List.mem_range.mpr hν')
    obtain ⟨f, hf, hx⟩ := bind_some hx
    cases hx
    have h0 := hz _ (List.mem_append_left _ (hin _ (List.mem_singleton.mpr rfl)))
    rw [Aff.value_sub, Aff.value_slot] at h0
    rw [sub_eq_zero.mp h0]
    unfold Env.rowR at hf
    have h5 : (X.p.v.y.h.xl == 5) = true := by rw [F.xl]; rfl
    rw [if_pos h5] at hf
    obtain ⟨row, hr, e⟩ := map_some hf
    subst e
    obtain ⟨trow, _, _, hrow, hm, T, hJ, _⟩ := F.rowTab
    obtain ⟨b, hb'⟩ := row5At_found hr
    obtain ⟨cell, rfl, hD⟩ := row5At_cells (D := X.D) (u := pt X.ρ X.c.rt) hb' hrow hJ T
      (by rw [hm, X.Z.lT]; exact T2.ar b hb') hr
    exact (Hd.row5_R F.num hD).trans
      (Inst.Model.Ledger.ext_R X.D.lT (fun m i => led _ ν i m) _).symm
  · have hl2 : l' < X.p.v.y.LamM := by rw [F.LamM]; exact hl'
    obtain ⟨x, hx, hin⟩ := mem_flat hc (List.mem_range.mpr hl2)
    obtain ⟨f, hf, hx⟩ := bind_some hx
    cases hx
    have h0 := hz _ (List.mem_append_right _ (List.mem_append_left _
      (hin _ (List.mem_singleton.mpr rfl))))
    rw [Aff.value_sub, Aff.value_slot] at h0
    have e : X.tT.sEnd + X.iSc l' = X.tT.sEnd + X.p.v.y.NN * X.p.v.y.Lam + l' := by
      unfold Pub34.iSc
      omega
    rw [e, sub_eq_zero.mp h0]
    exact P.shA2 .sc rfl rfl hf
  · have hNE : X.p.v.y.h.NE = X.D.nx := F.NE
    have he2 : e < X.p.v.y.h.NE := by rw [hNE]; exact he
    have hl2 : l' < X.p.v.y.LamM := by rw [F.LamM]; exact hl'
    have hx2 : l' * X.p.v.y.h.NE + e < X.p.v.y.LamM * X.p.v.y.h.NE := by
      calc l' * X.p.v.y.h.NE + e < l' * X.p.v.y.h.NE + X.p.v.y.h.NE := by omega
        _ = (l' + 1) * X.p.v.y.h.NE := by ring
        _ ≤ X.p.v.y.LamM * X.p.v.y.h.NE := Nat.mul_le_mul_right _ hl2
    obtain ⟨x, hx, hin⟩ := mem_flat hd (List.mem_range.mpr hx2)
    obtain ⟨f, hf, hx⟩ := bind_some hx
    cases hx
    have h0 := hz _ (List.mem_append_right _ (List.mem_append_right _
      (hin _ (List.mem_singleton.mpr rfl))))
    rw [Aff.value_sub, Aff.value_slot] at h0
    have e1 : X.tT.sEnd + X.iSel l' e =
        X.tT.sEnd + X.p.v.y.NN * X.p.v.y.Lam + X.p.v.y.LamM + (l' * X.p.v.y.h.NE + e) := by
      unfold Pub34.iSel
      omega
    have d1 : (l' * X.p.v.y.h.NE + e) / X.p.v.y.h.NE = l' := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt he2, Nat.zero_add]
    have d2 : (l' * X.p.v.y.h.NE + e) % X.p.v.y.h.NE = e := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he2]
    rw [d1, d2] at hf
    rw [e1, sub_eq_zero.mp h0]
    exact P.shA2 .sel rfl rfl hf

end OnBytes.Road.Rows
