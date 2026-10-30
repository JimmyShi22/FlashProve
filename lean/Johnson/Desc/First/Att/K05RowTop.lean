-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowTop.lean: K05_whole_any (Att/K05WholeAny.lean) and K05_port_top
(Att/K05PortTop.lean) laid into one
statement: the twin of K05_row_name (Att/K05RowName.lean) with the port's public premises paid.

Main names:
  `GatheredTop`: what stands behind the kind, at given entries of the vector of tables, a ledger, a
    record and lists: for all
    typed data with the four ties there are leftP's rows and a record of the gathering with: LeftIs;
      which record the runs
    read; the returns of pointsOf, of the runs "first", "second", "keys" and of Look.joinF; AllZero;
      the two points' texts; the
    join's form worth 0; hjv (the join's worth at what the lookup heard is its worth at the letters
      of Q, for all key values); Agree.
  `K05_port_top'`: K05_port_top at parameters whose two numbers are named, with GatheredTop as one
    premise and the claims paid.
  `RowTopSays`, `K05_row_top`: where the written piece says yes, outside the written counts bearErr,
    at every later ledger with
    as many slots and all entries of the vector of tables: GatheredTop gives the chain's first
      joint's Todo.

Premises of K05_row_top. Public: kap = 4; the plan's record; shapeHid's return; PlanLaw; the base
parameters' sizes, calls and
numbers; three UnitIs; Fits with the two block sizes; hscl. At each statement with "on": the ledger
in front is Sized and has two
given numbers; K3Pts. The seam; the written rounds are Plain with the kind's entries.
None of these, and no conjunct of GatheredTop, is shown in this file or in what it imports.
That GatheredTop is ever met at a view that the verifier accepts is not shown.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowName
import Johnson.Desc.First.Att.K05PortTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PlanLaw AllZero)
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA)

variable {M0 Mg X : Type}

/-- **What stands behind the kind, the port's public premises paid.** entry: the world's entries of
the vector of tables. It is
vacuous where no typed data have the four ties; at a yes of the piece there are such data
(LeadsSaysCl), and it is spent at
these. -/
def GatheredTop (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Q : JoinLay (closedOf P0 Λ ns N))
    (zk : Array (Array E)) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (G : Fork) (h : Heard) (L : Lists) (x0 : X) (m : Mg) : Prop :=
  ∀ (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail),
    UnitsOfP ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units →
    TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L →
    UnitsVals ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])) →
    TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))) →
    ∃ (l : Left) (A : Attention.Plan) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) (l₁ l₂ : List Aff) (jn : Runs.JoinsP)
      (k3 : Runs.PadIn) (kf : Array Aff) (Fj : Fork) (tj : OnBytes.K.Kc.Tape) (xj : Aff × Fork × OnBytes.K.Kc.Tape),
      LeftIs (geoOf S) zk h G l ∧ i.g = geoOf S ∧ i.zk = gL.zk ∧ gL.zk = zk ∧ A.NC = S.calls.size ∧
      pointsOf i.g zk h l = some i.p ∧ Runs.firstRun i Kc = some (l₁, jn) ∧ Runs.secondRun i Kc = some l₂ ∧
      AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂) ∧
      (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d ∧
      (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d ∧
      Runs.keysRun i k3 jn = some kf ∧ VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0 ∧
      (∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry)) =
        Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ ns N).msg m))) ∧
      Cb.Sub.Agree (attA Ly (runHeard (closedOf P0 Λ ns N) x0 du dt)) ((closedOf P0 Λ ns N).msg m) (K5Law.uAt (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (OnBytes.Road.Rows.tabOfAtt (oldOf S gL i)) (OnBytes.Road.Rows.placeAtt S))

/-- K05_port_top at parameters whose two numbers are named. -/
theorem K05_port_top' (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (ns : ℕ) (N : Nums)
    (hns : G.ns = ns) (hNn : numsOf h = N) (hk4 : P0.kap = 4) (rows : ℕ) {S : Attention.Shape} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs))
    (PL : PlanLaw cf S fs) (hDS : P0.D = OnBytes.Road.L5.dimOf S)
    (hC : P0.C = OnBytes.Road.L5.callsOf fs) (hnpl : P0.npl = 2) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (UD : UnitIs P0.D P0.C .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    {L : Lists} (b2 : Said (recOf (closedOf P0 Λ ns N) rows) h G L) (b3 : Sized G) {zx zy : Array E} {zk : Array (Array E)} (x0 : X)
    (H3 : K3Pts fs zx zy zk (P0.zOf x0)) (m : Mg)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns N) J₂} {Q : JoinLay (closedOf P0 Λ ns N)} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0)
    {entry : ℕ → ℕ → ℕ → Cb.Gl.E} (hga : GatheredTop P0 Λ ns N rows S Ly Q zk entry G h L x0 m)
    (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (x0, [])))) :
    ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ ns N) x0 du dt),
      (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ ns N) x0 du dt)) f).Holds ((closedOf P0 Λ ns N).msg m) := by
  subst hns hNn
  obtain ⟨cu, ct⟩ := claims_of_ties (closedOf P0 Λ G.ns (numsOf h)) hk4 rows b2 nz x0 du dt d1 d2 d3 d4
  obtain ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hptM, hptD, hk, hx, hv, hjv,
    hA⟩ := hga nz du dt d1 d2 d3 d4
  exact K05_port_top P0 Λ hk4 rows b2 b3 hid PL hDS hC hnpl hlt hNP x0 H3 UW UM UD nz du dt d1 d2 d3 d4 cu ct li m entry A
    gL hg hz hzk hN hP h1 h2 hZ hptM hptD hk hx hv hFit hls hlm hscl hjv hA

section Name
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel

/-- Q: the seat has laid (h, G); Said; and at every later ledger G' with G's slots and all entries
of the vector of tables:
GatheredTop gives the chain's first joint's Todo. -/
def RowTopSays {St Aa Bb : Type} (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ)
    (S : Attention.Shape) {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Q : JoinLay (closedOf P0 Λ ns N))
    (seat : Seat St) (x : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (mOf : Aa → Mg)
    (zk : Aa → Array (Array E)) (a : Aa) (b : Bb) : Prop :=
  ∃ (F G : Fork) (h : Heard) (L : Lists), seat.ledger (recA a) = some F ∧ seat.lay (recA a) h G = some (recB b) ∧
    Said x h G L ∧
    ∀ (G' : Fork) (entry : ℕ → ℕ → ℕ → Cb.Gl.E), Stays G G' → Sized G' → G'.ns = G.ns →
      GatheredTop P0 Λ ns N rows S Ly Q (zk a) entry G' h L (x0 a) (mOf a) →
      ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (mOf a)

/-- **The two laid into one, the port's public premises paid.** -/
theorem K05_row_top {St Aa Bb : Type} (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ)
    (hk4 : P0.kap = 4) (rows : ℕ) {S : Attention.Shape} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs))
    (PL : PlanLaw cf S fs) (hDS : P0.D = OnBytes.Road.L5.dimOf S)
    (hC : P0.C = OnBytes.Road.L5.callsOf fs) (hnpl : P0.npl = 2) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (UD : UnitIs P0.D P0.C .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    (hrec : p.own = recOf (closedOf P0 Λ ns0 (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns0 (numsPlan p.own k0)) J₂} {Q : JoinLay (closedOf P0 Λ ns0 (numsPlan p.own k0))} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowTopSays P0 Λ ns0 (numsPlan p.own k0) rows S Ly Q seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  refine (K05_whole_any (closedOf P0 Λ ns0 (numsPlan p.own k0)) hk4 rows seat p hrec Ex ds out recA recB x0 yOf mOf on
    (fun a ha F hF => (hon a ha F hF).1) hyes hpass hd he hFit).conseq (fun _ h => h) ?_
  rintro a τ b ha _ ⟨F, G, h, L, a1, a3, c2, ⟨_, n2, n1⟩, nz, du, dt, t1, t2, t3, t4, himp⟩
  obtain ⟨_, e1, e2⟩ := hon a ha F a1
  refine ⟨F, G, h, L, a1, a3, c2, fun G' entry hst zG' hns' hga => himp ?_⟩
  have c2' := said_congr hrec (c2.mono hst)
  have t2' := tailOfP_congr hrec t2
  have t1' := t1
  rw [show p.own.score = (recOf (closedOf P0 Λ ns0 (numsPlan p.own k0)) rows).score from congrArg (·.score) hrec] at t1'
  exact K05_port_top' P0 Λ ns0 (numsPlan p.own k0) (by rw [hns', n2, e1]) (by rw [n1, e2]) hk4 rows hid PL hDS hC hnpl hlt
    hNP UW UM UD c2' zG' (x0 a) (hk3 a ha) (mOf a) hFit hls hlm hscl hga nz du dt t1' t2' t3 t4

end Name

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_row_top
