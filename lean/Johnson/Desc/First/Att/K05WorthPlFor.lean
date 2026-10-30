-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05WorthPlFor.lean: kind K5: WHAT "the gathering's returns" (Returns,
Att/K05GatheredZero.lean) AND "what stays asked of the relation behind the kind" (BillsWorthJ,
Att/K05BillsWorth.lean) READ OF THE PLAN THAT THEY ARE HANDED WHOLE: ITS NUMBER OF CALLS NC, AND NOTHING ELSE.
So they are the same at two plans with one NC: among them a plan and the same plan with another list plFor in
its smallness test's record (the public's plan against the planner's return).

Main names:
  `returns_nc`: A'.NC = A.NC → (Returns … A' … ↔ Returns … A …).
  `billsWorthJ_nc`: A'.NC = A.NC → (BillsWorthJ … A' … ↔ BillsWorthJ … A …).
  `returns_plFor`, `billsWorthJ_plFor`: at { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } }.
  `billsWorthJ_withNC`: at the form in which K5Behind.worth (Att/K05LawOne.lean) hands the plan in:
    { A with NC := n } and { A' with NC := n }: the same at ANY two plans.
  `returns_nc_bites`: a control: with another NC the returns cannot both hold.
Limits. ON THE PLAN's ARGUMENT ALONE. BOTH TAKE THE SMALLNESS TEST's RECORD tl AS A LETTER OF ITS OWN, and
BillsWorthJ reads it in TYPES too (JAtt x.ns tl; attLin x S tl …; entryOf … tl …): that these read no plFor of
THAT letter is not said here: whoever moves tl from the planner's to the public's record owes it. EMPTY? Each is
an equivalence: where neither side holds it says nothing; the control shows that NC is truly read.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05BillsWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.First.Look (Sent attSg JAtt)

section
variable {S : Attention.Shape} {zx : Array E} {zk : Array (Array E)} {G : Fork} {h : Heard} {l : Left}
  {gL : Forest.Heard} {i : Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : Runs.JoinsP} {k3 : Runs.PadIn}
  {kf : Array Aff} {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
  {tl : HTailF2} {nW : ℕ} {lk : LookIn}

theorem returns_nc_of {A A' : Attention.Plan} (e : A'.NC = A.NC) (eu : A'.iU3 = A.iU3)
    (R : Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk) :
    Returns S zx zk G h l A' gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk :=
  ⟨R.left, R.geo, R.zkI, R.zkL, e.trans R.nc, R.points, R.first, R.second, R.keys, R.join, R.tables,
    R.zx, R.mats, R.u3.trans eu.symm⟩

/-- **The returns read of the plan its number of calls alone.** -/
theorem returns_nc {A A' : Attention.Plan} (e : A'.NC = A.NC) (eu : A'.iU3 = A.iU3) :
    Returns S zx zk G h l A' gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk ↔
      Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk :=
  ⟨returns_nc_of e.symm eu.symm, returns_nc_of e eu⟩

theorem returns_plFor (A0 : Attention.Plan) (pf : Array PlaceF) :
    Returns S zx zk G h l
        { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } } gL i Kc l₁ l₂ jn
        k3 kf Fj tj xj tl nW lk ↔
      Returns S zx zk G h l A0 gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk :=
  returns_nc rfl rfl

/-- A control: with another number of calls the two cannot both hold. -/
theorem returns_nc_bites {A A' : Attention.Plan} (e : A'.NC ≠ A.NC)
    (R : Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk) :
    ¬ Returns S zx zk G h l A' gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk :=
  fun R' => e (R'.nc.trans R.nc.symm)

end

section
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)
variable {St Aa Bb W : Type} (S : Attention.Shape) (ns : ℕ) (N : Nums) (Kc : ℕ) (k3 : Runs.PadIn)
  (nW : ℕ) (tj : OnBytes.K.Kc.Tape) (gOf : Aa → Forest.Heard) (lk0 : Aa → LookIn) (seat : Seat St)
  (xr : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St) (on : Aa → Prop)
  (part : W → (attSg x D rad).Msg) (R' : Bb → W → Prop)

theorem billsWorthJ_nc_of {A A' : Attention.Plan} (e : A'.NC = A.NC) (eu : A'.iU3 = A.iU3)
    (H : BillsWorthJ x tl D rad Ex Wp α S ns N A Kc k3 nW tj gOf lk0 seat xr recA recB on part R') :
    BillsWorthJ x tl D rad Ex Wp α S ns N A' Kc k3 nW tj gOf lk0 seat xr recA recB on part R' :=
  fun a b w ha hR F G h L h1 h2 h3 h4 h5 l i l₁ l₂ jn kf xj Rt =>
    H a b w ha hR F G h L h1 h2 h3 h4 h5 l i l₁ l₂ jn kf xj (returns_nc_of e.symm eu.symm Rt)

/-- **What stays asked of the relation behind reads of the plan its number of calls alone.** -/
theorem billsWorthJ_nc {A A' : Attention.Plan} (e : A'.NC = A.NC) (eu : A'.iU3 = A.iU3) :
    BillsWorthJ x tl D rad Ex Wp α S ns N A' Kc k3 nW tj gOf lk0 seat xr recA recB on part R' ↔
      BillsWorthJ x tl D rad Ex Wp α S ns N A Kc k3 nW tj gOf lk0 seat xr recA recB on part R' :=
  ⟨billsWorthJ_nc_of x tl D rad Ex Wp α S ns N Kc k3 nW tj gOf lk0 seat xr recA recB on part R' e.symm
      eu.symm,
    billsWorthJ_nc_of x tl D rad Ex Wp α S ns N Kc k3 nW tj gOf lk0 seat xr recA recB on part R' e eu⟩

theorem billsWorthJ_plFor (A0 : Attention.Plan) (pf : Array PlaceF) :
    BillsWorthJ x tl D rad Ex Wp α S ns N
        { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } } Kc k3 nW tj gOf lk0
        seat xr recA recB on part R' ↔
      BillsWorthJ x tl D rad Ex Wp α S ns N A0 Kc k3 nW tj gOf lk0 seat xr recA recB on part R' :=
  billsWorthJ_nc x tl D rad Ex Wp α S ns N Kc k3 nW tj gOf lk0 seat xr recA recB on part R' rfl rfl

/-- In the form in which K5Behind.worth hands the plan in: the same at any two plans. -/
theorem billsWorthJ_withNC (A A' : Attention.Plan) (n : ℕ) (eu : A'.iU3 = A.iU3) :
    BillsWorthJ x tl D rad Ex Wp α S ns N { A' with NC := n } Kc k3 nW tj gOf lk0 seat xr recA recB on
        part R' ↔
      BillsWorthJ x tl D rad Ex Wp α S ns N { A with NC := n } Kc k3 nW tj gOf lk0 seat xr recA recB on
        part R' :=
  billsWorthJ_nc x tl D rad Ex Wp α S ns N Kc k3 nW tj gOf lk0 seat xr recA recB on part R' rfl eu

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.returns_nc
#print axioms VerifiableInference.Desc.First.Att.P.returns_plFor
#print axioms VerifiableInference.Desc.First.Att.P.returns_nc_bites
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_nc
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_plFor
#print axioms VerifiableInference.Desc.First.Att.P.billsWorthJ_withNC
