-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Planned.lean: K05_row_plan (Att/K05RowBase.lean) and K05_keepsW_plan
(Att/K05KeepsTop.lean) at a plan that
the planner returns: the shape's return and the plan's record are paid (plan_shape,
Johnson/Road/Lane5AttPlan.lean; rec_of_plan,
Att/K05Record.lean).

Main names:
  `rec_at_caller`: the plan's record at the caller over the committed symbols.
  `K05_row_planned`, `K05_keepsW_planned`.
  `K05_keepsW_one`: the last with the two public tests as one Boolean (Att/K05PlanAll.lean:
    planOkAll) and the ledger in front by
    one record (Att/K05Room.lean: Room; its fourth field, the free slots, is idle here: decide's yes
      already says that the hearing
    found room).

Public premises left: Attention.plan settings i cf = ok A; p.own = A.own; PlanLaw and unitsOk (or
planOkAll); hscl.
The planner stands here as a premise on a return, not as a text that decides: the plan is made
outside the kind's block; that it
is made so is its maker's to show. planOkAll is evaluated in no file of this tree.
What the heads of Att/K05RowTop.lean and Att/K05KeepsTop.lean say is not shown is not shown here
either.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsTop
import Johnson.Desc.First.Att.K05Record
import Johnson.Desc.First.Att.K05PlanAll
import Johnson.Desc.First.Att.K05Room

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

/-- The plan's record at the caller. -/
theorem rec_at_caller {s : Size} {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (PL : PlanLaw cf A.S A.fs) (hU : unitsOk A.S A.fs = true)
    (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E) (Λ : Lin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Mg) (ns : ℕ) (N : Nums) :
    A.own = recOf (closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ ns N) A.own.rows := by
  obtain ⟨_, _, _, _, _, _, _, U⟩ := units_all hU
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  exact rec_of_plan hA PL.place (OnBytes.Road.Rows.norm_of_hid hid)
    (Nat.le_of_succ_le (OnBytes.Road.Rows.sizes_of_hid hid).lnT) U _ rfl rfl rfl

open Classical in
/-- **K05_row_plan at a plan that the planner returns.** -/
theorem K05_row_planned {St Aa Bb : Type} {s : Size} {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A) (PL : PlanLaw cf A.S A.fs)
    (hU : unitsOk A.S A.fs = true) (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E)
    (Λ0 : Lin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Mg) (seat : Seat St) (p : Par) (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS)
    (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S
        (endLay (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) (cellAt A.S pl) A.S.ls A.S.cf.lmS j0) (meantQ (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0)
        seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_row_plan (OnBytes.Road.L5.plan_shape hA).1 PL pl zOf Λ0 seat p ns0 k0 Q0 j0 A.own.rows hU
    (hp.trans (rec_at_caller hA PL hU pl zOf _ _ _)) Ex ds out recA recB x0 yOf mOf zx zy zk on hon hk3 hyes hpass hd he hscl

open Classical in
/-- **K05_keepsW_plan at a plan that the planner returns.** -/
theorem K05_keepsW_planned {St Aa Bb W : Type} {s : Size} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A)
    (PL : PlanLaw cf A.S A.fs) (hU : unitsOk A.S A.fs = true) (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E)
    (Λ0 : Lin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Mg) (seat : Seat St) (p : Par) (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS)
    (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0)
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsTop (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S
      (endLay (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) (cellAt A.S pl) A.S.ls A.S.cf.lmS j0) (meantQ (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0)
      seat p.own recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) :=
  K05_keepsW_plan (OnBytes.Road.L5.plan_shape hA).1 PL pl zOf Λ0 seat p ns0 k0 Q0 j0 A.own.rows hU
    (hp.trans (rec_at_caller hA PL hU pl zOf _ _ _)) Ex ds out recA recB x0 yOf zx zy zk on hon hk3 hyes hpass hd he hscl part
    mOf on' R' hon' hb pin

open Classical in
/-- **The same, the two public tests as one Boolean (Att/K05PlanAll.lean: planOkAll), and the ledger
in front by one record
(Att/K05Room.lean: Room).** -/
theorem K05_keepsW_one {St Aa Bb W : Type} {s : Size} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A)
    (hok : planOkAll cf A.S A.fs = true) (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E)
    (Λ0 : Lin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Mg) (seat : Seat St) (p : Par) (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ (OnBytes.Road.L5.dimOf A.S) A.S.ls A.S.cf.lmS)
    (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (kr : ℕ) (hroom : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Room F ns0 k0 kr)
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0)
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsTop (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S
      (endLay (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) (cellAt A.S pl) A.S.ls A.S.cf.lmS j0) (meantQ (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0)
      seat p.own recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) A.S pl (OnBytes.Road.L5.callsOf A.fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  have h2 := hok
  unfold planOkAll at h2
  rw [Bool.and_eq_true] at h2
  exact K05_keepsW_planned hA (K5Law.plan_law (OnBytes.Road.L5.plan_shape hA).1 h2.1) h2.2 pl zOf Λ0 seat p hp ns0 k0 Q0 j0 Ex ds
    out recA recB x0 yOf zx zy zk on (fun a ha F hF => ⟨(hroom a ha F hF).sized, (hroom a ha F hF).ns, (hroom a ha F hF).next⟩)
    hk3 hyes hpass hd he hscl part mOf on' R' hon' hb pin

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_row_planned
#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_planned
#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_one
