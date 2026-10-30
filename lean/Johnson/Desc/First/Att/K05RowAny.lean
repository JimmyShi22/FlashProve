-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowAny.lean: `K05_row_top` (Johnson/Desc/First/Att/K05RowTop.lean) and the
forms above it at any parameters that are a base: one statement each, of which the forms at `baseOf`
(Johnson/Desc/First/Att/K05RowBase.lean, Johnson/Desc/First/Att/K05KeepsTop.lean,
Johnson/Desc/First/Att/K05Planned.lean) and at `attBase` (Johnson/Desc/First/Att/K05RowAtt.lean) are
instances.

Definitions, statements and proofs.
Main names:
  `BaseIs P0 S fs cellJ0`: five ties on the letters: kap = 4; D = dimOf S; C = callsOf fs; two plane
    messages; the cells are read at the places cellJ0.
  `baseIs_base`: `baseOf` is a base.
  `seven_of`: the seven premises of `closed_fits` (Johnson/Desc/First/Att/K05Fits.lean) at any base,
    from "`shapeHid` has returned (S, fs)" and `CallsFit`. (`seven_at_base`,
    Johnson/Desc/First/Att/K05SevenAt.lean, is this at `baseOf`; the proof's text stands in both
    files.)
  `K05_row_any`: `K05_row_top` at P0, with the linear claims `meantLin`, the end's letters `endLay`
    at cellJ0, S.ls and S.cf.lmS, and the join's letters `meantQ`.
  `K05_row_any_plan`: the same with `PlanLaw` and the three `UnitIs` paid by a yes of `planOkAll`.
  `K05_keepsW_any`: the form for the table of joints (KeepsW) at any base, from a yes of
    `planOkAll`; `BillsTop` (Johnson/Desc/First/Att/K05KeepsTop.lean) is taken as it stands.
  `K05_keepsW_any_one`: the same at a plan that `Attention.plan` returns: that return pays the
    return of `shapeHid` and, by `rec_of_plan` (Johnson/Desc/First/Att/K05Record.lean), the plan's
    record; the ledger in front by `Room`.
The four statements are those of `K05_row_base`, `K05_row_plan`, `K05_keepsW_plan` and
`K05_keepsW_one` with `baseOf` … turned into the letter P0; in the second and the third `PlanLaw`
and `unitsOk` are also packed into `planOkAll`.
Used: `K05_row_top`, `closed_fits`, `plan_all`, `unitIs_m1`, `unitIs_d1`,
`place_scores`, `rec_of_plan`, `plan_shape`, `keepsW_of_pinned`, `sizes_of_hid`, `norm_of_hid`,
`lT_le_16`, `callsFit_a01`, `callsFit_deep`; no routine in a context.
Limits: those of Johnson/Desc/First/Att/K05RowTop.lean, Johnson/Desc/First/Att/K05KeepsTop.lean and
Johnson/Desc/First/Att/K05Planned.lean. No soundness of the protocol is claimed: the seam and the
premises named are not shown. Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PlanAll
import Johnson.Desc.First.Att.K05SevenAt
import Johnson.Desc.First.Att.K05RowTop
import Johnson.Desc.First.Att.K05Fits
import Johnson.Desc.First.Att.K05KeepsTop
import Johnson.Desc.First.Att.K05Record
import Johnson.Desc.First.Att.K05Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (callsOf CallsFit dimOf)
open K5Law (PlanLaw)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open Cb.Pv.Tail (Size JCell)

variable {M0 Mg X : Type}

/-- **A base**: five ties on the letters. -/
structure BaseIs (P0 : OwnPar Cb.Gl.E M0 X) (S : Attention.Shape) (fs : Model.Forest.Shape)
    (cellJ0 : AttSeg.Raw → P0.J) : Prop where
  kap : P0.kap = 4
  D : P0.D = dimOf S
  C : P0.C = callsOf fs
  npl : P0.npl = 2
  rd : ∀ e, P0.rd e = rdOf cellJ0 e

/-- baseOf is a base. -/
theorem baseIs_base {s : Size} (S : Attention.Shape) (fs : Model.Forest.Shape) (pl : ℕ → ℕ → ℕ → JCell s)
    (zOf : X → ℕ → Cb.Gl.E) : BaseIs (baseOf (K := Cb.Gl.E) S pl (callsOf fs) 2 zOf) S fs (cellAt S pl) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

section Any
variable {P0 : OwnPar Cb.Gl.E M0 X} {S : Attention.Shape} {fs : Model.Forest.Shape} {cellJ0 : AttSeg.Raw → P0.J}

/-- **The seven, at any base.** -/
theorem seven_of (B : BaseIs P0 S fs cellJ0) {lid : ℕ} {cf : Attention.Cfg}
    (hh : Attention.shapeHid lid cf = Except.ok (S, fs)) (hf : CallsFit S fs) :
    (∀ e, P0.rd e = rdOf cellJ0 e) ∧ S.ls ≤ P0.D.ln ∧ (∀ u : AttSeg.Fam, IsPlane u → S.cf.lmS ≤ u.l P0.D) ∧
    P0.C.a 0 = P0.C.a 1 ∧ (∀ u : AttSeg.Fam, IsPlane u → u.l P0.D ≤ P0.C.a u.call) ∧
    P0.D.lT ≤ 2 ^ P0.kap ∧ P0.npl = 2 := by
  have Z := OnBytes.Road.Rows.sizes_of_hid hh
  have N := OnBytes.Road.Rows.norm_of_hid hh
  have hD : S.cf.lmS ≤ (dimOf S).lD := by
    have e : (dimOf S).lD = S.nD := N.nD.symm
    rw [e]
    exact Z.lmS
  have hM : (dimOf S).lD ≤ (dimOf S).lM := by
    unfold Dim.lD Dim.lM
    omega
  rw [B.D, B.C, B.kap]
  refine ⟨B.rd, Z.ls, fun u hu => ?_, OnBytes.Road.L5.callsFit_a01 hf,
    fun u _ => le_trans (OnBytes.Road.L5.callsFit_deep hf u) (hf.2.1 u.call), ?_, B.npl⟩
  · cases u with
    | m1 => exact le_trans hD hM
    | d1 => exact hD
    | m2 => exact le_trans hD hM
    | d2 => exact hD
    | w3 => exact hu.elim
    | x3 => exact hu.elim
    | f4 => exact hu.elim
  · have := lT_le_16 hh
    omega

open Classical in
/-- **K05_row_top at any parameters that are a base**, with the meant linear claims. -/
theorem K05_row_any {St Aa Bb : Type} (B : BaseIs P0 S fs cellJ0) {lid : ℕ} {cf : Attention.Cfg}
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs) (Λ0 : Lin P0 Mg) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D S.ls S.cf.lmS) (rows : ℕ) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl →
      UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf fs) .w3 qW wl)
    (UM : UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf fs) .m1 qM
      ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm))
    (UD : UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf fs) .d1 qD
      ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    (hrec : p.own = recOf (closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0
      (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str)
    (mOf : Aa → Mg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = S.cf.sh.getD 0 0) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) rows S
        (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)
          cellJ0 S.ls S.cf.lmS j0)
        (meantQ P0 Λ0 ns0 (numsPlan p.own k0)
          Q0)
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0
        (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := seven_of B hid PL.fit
  have hlt : S.cf.lt = P0.D.lT := by
    rw [B.D]
    exact (OnBytes.Road.Rows.norm_of_hid hid).lt
  have hNP : (geoOf S).NP = (size18 P0.D).pairs := by
    rw [B.D]
    rfl
  exact K05_row_top P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) seat p ns0 k0 B.kap rows hid PL B.D B.C B.npl hlt hNP
    (by rw [B.D, B.C]; exact UW) (by rw [B.D, B.C]; exact UM) (by rw [B.D, B.C]; exact UD) hrec Ex ds out recA recB x0
    yOf mOf zx zy zk on hon hk3 hyes hpass hd he
    (closed_fits P0 Λ0 ns0 (numsPlan p.own k0) Q0 cellJ0 S.ls S.cf.lmS j0 s1 s2 s3 s4 s5 s6 s7) rfl rfl hscl


open Classical in
/-- **The same from one Boolean test on the plan**: planOkAll pays PlanLaw and the three public
records on units (after `K05_row_plan`, Johnson/Desc/First/Att/K05RowBase.lean). -/
theorem K05_row_any_plan {St Aa Bb : Type} (B : BaseIs P0 S fs cellJ0) {lid : ℕ} {cf : Attention.Cfg}
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (hp : planOkAll cf S fs = true) (Λ0 : Lin P0 Mg) (seat : Seat St) (p : Par)
    (ns0 k0 : ℕ) (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D S.ls S.cf.lmS) (rows : ℕ)
    (hrec : p.own = recOf (closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0
      (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str)
    (mOf : Aa → Mg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = S.cf.sh.getD 0 0) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) rows S
        (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)
          cellJ0 S.ls S.cf.lmS j0)
        (meantQ P0 Λ0 ns0 (numsPlan p.own k0)
          Q0)
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0
        (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  have A := plan_all hid hp
  obtain ⟨_, _, u1, u2, wl, _, _, U⟩ := A.units
  have h01 := OnBytes.Road.L5.callsFit_a01 A.law.fit
  have e := (K5Law.place_scores A.law.place).symm.trans U.sco
  obtain ⟨e1, e2⟩ : ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) = u1 ∧
      ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd) = u2 := by
    simp only [List.cons.injEq, and_true] at e
    exact e
  exact K05_row_any B hid A.law Λ0 seat p ns0 k0 Q0 j0 rows (qW := 2) (qM := 1) (qD := 1)
    (fun w hw => by
      rw [U.sWl] at hw
      rw [← Option.some.inj hw]
      exact U.w3)
    (by rw [e1]; exact unitIs_m1 h01 U.m2) (by rw [e2]; exact unitIs_d1 h01 U.d2) hrec Ex ds out recA recB x0 yOf mOf
    zx zy zk on hon hk3 hyes hpass hd he hscl

open Classical in
/-- **The kind's law in the form for the table of joints, at any base** (after `K05_keepsW_plan`,
Johnson/Desc/First/Att/K05KeepsTop.lean). -/
theorem K05_keepsW_any {St Aa Bb W : Type} (B : BaseIs P0 S fs cellJ0) {lid : ℕ} {cf : Attention.Cfg}
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (hp : planOkAll cf S fs = true)
    (Λ0 : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ) (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0)))
    (j0 : NameJ P0.D S.ls S.cf.lmS) (rows : ℕ)
    (hrec : p.own = recOf (closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsTop P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) rows S
      (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 S.ls S.cf.lmS j0) (meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0)
      seat p.own recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  refine Reduction.keepsW_of_pinned part mOf (fun m => ?_) pin
  refine Reduction.Leads.conseq (K05_row_any_plan B hid hp Λ0 seat p ns0 k0 Q0 j0 rows hrec Ex ds out recA recB x0 yOf
    (fun _ => m) zx zy zk on hon hk3 hyes hpass hd he hscl) (fun _ h => h)
    fun a τ b ha hout hq => ⟨hon' a τ b ha hout, fun w hw hR => ?_⟩
  obtain ⟨_, G, h, L, _, q2, q3, q4⟩ := hq
  obtain ⟨G', entry, g1, g2, g3, g4⟩ := hb a b w hR G h L q2 q3
  subst hw
  exact q4 G' entry g1 g2 g3 g4


open Classical in
/-- **The same at a plan that the planner returns, the ledger in front by one record** (after
`K05_keepsW_one`, Johnson/Desc/First/Att/K05Planned.lean). -/
theorem K05_keepsW_any_one {St Aa Bb W : Type} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A)
    (B : BaseIs P0 A.S A.fs cellJ0) (hok : planOkAll cf A.S A.fs = true)
    (Λ0 : Lin P0 Mg) (seat : Seat St) (p : Par) (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D A.S.ls A.S.cf.lmS)
    (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (kr : ℕ) (hroom : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Room F ns0 k0 kr)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0)
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsTop P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S
      (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 A.S.ls A.S.cf.lmS j0) (meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0)
      seat p.own recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  have Al := plan_all hid hok
  obtain ⟨_, _, _, _, _, _, _, U⟩ := Al.units
  have hrec : p.own = recOf (closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0))
      A.own.rows :=
    hp.trans <| rec_of_plan hA Al.law.place (OnBytes.Road.Rows.norm_of_hid hid)
      (Nat.le_of_succ_le (OnBytes.Road.Rows.sizes_of_hid hid).lnT) U _ B.D B.npl B.kap
  exact K05_keepsW_any B hid hok Λ0 seat p ns0 k0 Q0 j0 A.own.rows hrec Ex ds out recA recB x0 yOf zx zy zk on
    (fun a ha F hF => ⟨(hroom a ha F hF).sized, (hroom a ha F hF).ns, (hroom a ha F hF).next⟩) hk3 hyes hpass hd he hscl
    part mOf on' R' hon' hb pin

end Any

end VerifiableInference.Desc.First.Att.P
