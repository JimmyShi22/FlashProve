-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowBase.lean: K05_row_top (Att/K05RowTop.lean) at the caller over the
committed symbols (Att/K05Caller.lean:
baseOf S pl (callsOf fs) 2 zOf), the meant linear claims (Att/K05Meant.lean) and the library's own
record of names
(Att/K05Fits.lean: endLay).

Main names:
  `K05_row_base`: Fits is paid (closed_fits, its seven premises by seven_at_base,
    Att/K05SevenAt.lean); the two block sizes, kap = 4,
    the sizes, the calls, the two plane messages and the number of pairs hold by definition; lt by
      the shape's Norm.
  `K05_row_plan`: the same, the three UnitIs paid by a yes of one Boolean test on the place
    (Att/K05UnitsOk.lean: unitsOk).

Premises of K05_row_plan. Public: shapeHid's return; PlanLaw; unitsOk S fs = true; the plan's
record; hscl. At each statement with
"on": the ledger in front is Sized and has two given numbers; K3Pts. The seam; the written rounds
are Plain with the kind's entries.
Letters: pl (where a cell lies among the committed symbols); zOf (the lookup's end point in a
statement); the two readings of Λ0
(the mask; the symbols); Q0 (the lookup's letters in the join); j0 (some late entry).
What Att/K05RowTop.lean's head says is not shown is not shown here either. unitsOk is evaluated in
no file of this tree.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowTop
import Johnson.Desc.First.Att.K05SevenAt
import Johnson.Desc.First.Att.K05UnitsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (recOf)
open K5Law (PlanLaw)
open Cb.Pv.Att.End (JoinLay NameJ)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open Cb.Pv.Tail (Size JCell)

variable {Mg X : Type}

open Classical in
/-- **K05_row_top at the caller over the committed symbols.** -/
theorem K05_row_base {St Aa Bb : Type} {s : Size} {S : Attention.Shape} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E)
    (Λ0 : Lin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ) (Q0 : JoinLay (closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0)))
    (j0 : NameJ (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS) (rows : ℕ)
    {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl →
      UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf fs) .w3 qW wl)
    (UM : UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf fs) .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm))
    (UD : UnitIs (OnBytes.Road.L5.dimOf S) (OnBytes.Road.L5.callsOf fs) .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    (hrec : p.own = recOf (closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = S.cf.sh.getD 0 0) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) rows S
        (endLay (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) (cellAt S pl) S.ls S.cf.lmS j0) (meantQ (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0)
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := seven_at_base (K := Cb.Gl.E) hid PL.fit pl zOf
  exact K05_row_top (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) seat p ns0 k0 rfl rows hid PL rfl rfl rfl (OnBytes.Road.Rows.norm_of_hid hid).lt rfl UW UM
    UD hrec Ex ds out recA recB x0 yOf mOf zx zy zk on hon hk3 hyes hpass hd he
    (closed_fits (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0 (cellAt S pl) S.ls S.cf.lmS j0 s1 s2 s3 s4 s5 s6 s7) rfl rfl hscl

open Classical in
/-- **The same, the three public records on units paid by one Boolean test on the place**
(Att/K05UnitsOk.lean). -/
theorem K05_row_plan {St Aa Bb : Type} {s : Size} {S : Attention.Shape} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E)
    (Λ0 : Lin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ) (Q0 : JoinLay (closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0)))
    (j0 : NameJ (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS) (rows : ℕ)
    (hU : unitsOk S fs = true)
    (hrec : p.own = recOf (closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = S.cf.sh.getD 0 0) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) rows S
        (endLay (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) (cellAt S pl) S.ls S.cf.lmS j0) (meantQ (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0)
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  obtain ⟨_, _, u1, u2, wl, _, _, U⟩ := units_all hU
  have h01 := (seven_at_base (K := Cb.Gl.E) (X := X) hid PL.fit pl zOf).2.2.2.1
  have e := (K5Law.place_scores PL.place).symm.trans U.sco
  obtain ⟨e1, e2⟩ : ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) = u1 ∧ ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd) = u2 := by
    simp only [List.cons.injEq, and_true] at e
    exact e
  exact K05_row_base hid PL pl zOf Λ0 seat p ns0 k0 Q0 j0 rows (qW := 2) (qM := 1) (qD := 1)
    (fun w hw => by
      rw [U.sWl] at hw
      rw [← Option.some.inj hw]
      exact U.w3)
    (by rw [e1]; exact unitIs_m1 h01 U.m2) (by rw [e2]; exact unitIs_d1 h01 U.d2) hrec Ex ds out recA recB x0 yOf mOf zx zy zk
    on hon hk3 hyes hpass hd he hscl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_row_plan
#print axioms VerifiableInference.Desc.First.Att.P.K05_row_base
