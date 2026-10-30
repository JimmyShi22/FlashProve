-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RowName.lean: K05_whole_any (Att/K05WholeAny.lean) and K05_port
(Att/K05Port.lean) laid into one statement.
Where the written piece says yes, outside the written counts bearErr, at every later ledger G'
(Stays G G', Sized G', as many
slots as G) and all entries of the vector of tables: every gathered form worth 0 in the world of G',
the tables true (Agree), the join and the port's public ties
give the chain's first joint's Todo.

Main names:
  `claims_of_ties`: the letters' claims follow from Said and the four ties.
  `Gathered`: what stands behind the kind, at given entries of the vector of tables, a ledger, a
    record and lists: for all
    typed data with the four ties there are leftP's rows and a record of the gathering with: LeftIs;
      pointsOf's and the two runs' return;
    AllZero; AttPub; the two points' texts; two ties of the lookup's inner point; PtsAre and SlotsH;
      joinF; Agree.
  `K05_port'`: K05_port at parameters whose two numbers are named, with Gathered as one premise and
    the claims paid.
  `said_congr`, `tailOfP_congr`.
  `RowNameSays`, `K05_row_name`.

Premises of K05_row_name: kap = 4; the plan's record; public numbers of the shape; the ledger in
front is Sized and has two
given numbers; the lookup's points at the first statement (LookPts, UnitPtsM, UnitPtsD); the seam
(out's yes is decide's yes on
"rvT (ckP .two) ds τ, digests struck", with roundsFit and every drawn triple below the prime; out's
yes gives that the tests
of work pass); the written rounds are Plain with the kind's entries; Fits, and the two block sizes
are the shape's.
None of these, and no conjunct of Gathered, is shown in this file or in what it imports.
That Gathered is ever met at a view that the verifier accepts is not shown.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WholeAny
import Johnson.Desc.First.Att.K05Port

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf ownAt_fits)
open VerifiableInference.Desc.Part
open K5Law (oldOf AllZero sixAt PtsAre SlotsH uAt)
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA joinF)
open OnBytes.Road (pt)
open OnBytes.Road.Rows (AttPub tabOfAtt placeAtt)
open Inst.Model.AttSeg (yn yi')

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 Mg X : Type}

/-- **The letters' claims, from Said and the four ties.** -/
theorem claims_of_ties (P : OwnPar K Mg X) (hk4 : P.kap = 4) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (b2 : Said (recOf P rows) h G L) (nz : BetasNz ρ L) (x0 : X)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)
    (d1 : UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du (recOf P rows).score h.scores.toList L.planes.flatten
      L.units) (d2 : TailOfP dt (recOf P rows) h L)
    (d3 : UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
      (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
      (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])))) :
    UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) ∧
      dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])) := by
  have hne : (recOf P rows).score ≠ [] := by simp [recOf]
  obtain ⟨_, ft⟩ := fits_of_own (P.own (theMeans K P.D P.C P.kap)) _ (ownAt_fits P _ hk4 rows) hne
  obtain ⟨e1, e2⟩ := tail_exists (P.own (theMeans K P.D P.C P.kap)).tail b2 hne nz ft
    (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
      (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])))
  obtain rfl : dt = tailData (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
      (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])) := tailH_one d2 e1 d4 e2
  exact ⟨(units_claims _ du _ _ _ _ (landedUnits P _) _ d1 d3).2
      (units_targets_of_last _ du _ _ _ _ _ (last_own _ _) b2.units d1),
    (tail_claims (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
      (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).2
      (value_tail_targets P _ rows b2 nz (landedTail P _) (fun i => by simp [landedTail, OnBytes.Tie.Pv.Att.sc3Num]) _)⟩

/-- **What stands behind the kind**, at a ledger G, a record h and lists L: for all typed data with
the four ties there are
the rows that leftP leaves and a record of the gathering at which: every gathered form is worth 0;
the
tables are true (Agree); the join holds; and the public ties of the port hold. entry: the world's
entries of the vector of
tables. It is vacuous where no typed data have the four ties; at a yes of the piece there are such
data (LeadsSaysCl), and it
is spent at these. -/
def Gathered (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape) (u1 u2 : UnitG)
    (ρ : Reading K) {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Q : JoinLay (closedOf P0 Λ ns N))
    (zk : Array (Array E)) (entry : ℕ → ℕ → ℕ → K) (G : Fork) (h : Heard) (L : Lists) (x0 : X) (m : Mg) : Prop :=
  ∀ (nz : BetasNz ρ L) (du : UnitsH ρ ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units) (dt : TailH ρ ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).tail),
    UnitsOfP ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units →
    TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L →
    UnitsVals ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units du (unitsAdd (ρ := ρ) ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])) →
    TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units du (x0, []))) →
    ∃ (l : Left) (A : Attention.Plan) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ)
      (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (r1 r2 : ℕ × CallG × Keys) (lid : ℕ) (cf : Attention.Cfg)
      (fs : Model.Forest.Shape),
      LeftIs (geoOf S) zk h G l ∧ i.g = geoOf S ∧ i.zk = gL.zk ∧ A.NC = S.calls.size ∧
      pointsOf i.g zk h l = some i.p ∧ Runs.firstRun i Kc = some (l₁, jn) ∧ Runs.secondRun i Kc = some l₂ ∧
      AllZero ρ (G.worldOf ρ (Λ.maskOf m) entry) (l₁ ++ l₂) ∧ i.g.units .kr [.rm, .rd] = [r1, r2] ∧
      AttPub ρ (oldOf S gL i) lid cf fs ∧
      (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d ∧
      (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d ∧
      (∀ j < S.cf.ldh, pt ρ (oldOf S gL i).d.zcW j = yn P0.D P0.C (P0.zOf x0) j) ∧
      (∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j = yi' (OnBytes.Road.L5.dimOf S) P0.C (P0.zOf x0) j) ∧
      (∀ a1 a2 k1 k2, h.remainders[0]? = some a1 → h.remainders[1]? = some a2 → i.p.scores[0]? = some k1 →
        i.p.scores[1]? = some k2 →
        PtsAre ρ (oldOf S gL i) (closedOf P0 Λ ns N) (runHeard (closedOf P0 Λ ns N) x0 du dt) (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2) ∧
        SlotsH (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) (closedOf P0 Λ ns N) (runHeard (closedOf P0 Λ ns N) x0 du dt) m
          (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2)
          (uAt (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (tabOfAtt (oldOf S gL i)) (placeAtt S))) ∧
      (joinF (J₂ := J₂) Q (runHeard (closedOf P0 Λ ns N) x0 du dt)).Holds (Sum.elim ((closedOf P0 Λ ns N).msg m)
        (uAt (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (tabOfAtt (oldOf S gL i)) (placeAtt S))) ∧
      Cb.Sub.Agree (attA Ly (runHeard (closedOf P0 Λ ns N) x0 du dt)) ((closedOf P0 Λ ns N).msg m)
        (uAt (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (tabOfAtt (oldOf S gL i)) (placeAtt S))

/-- K05_port at parameters whose two numbers are named. -/
theorem K05_port' (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (ns : ℕ) (N : Nums) (hns : G.ns = ns)
    (hNn : numsOf h = N) (hk4 : P0.kap = 4) (rows : ℕ) {L : Lists}
    (b2 : Said (recOf (closedOf P0 Λ ns N) rows) h G L) (b3 : Sized G) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (hlt : S.cf.lt = P0.D.lT) (hNP : (geoOf S).NP = (size18 P0.D).pairs)
    {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    (hG : S.G = 2 ^ S.cf.lgk) {zk : Array (Array E)} (x0 : X)
    (lpW : ∀ wl, (geoOf S).single .wl = some wl → LookPts ρ P0.D P0.C (P0.zOf x0)
      (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])))
    (lpM : UnitPtsM ρ P0.D P0.C (P0.zOf x0) u1 (zk.getD u1.call #[]))
    (lpD : UnitPtsD ρ P0.D P0.C (P0.zOf x0) u2 (zk.getD u2.call #[])) (m : Mg)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns N) J₂} {Q : JoinLay (closedOf P0 Λ ns N)} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS)
    {entry : ℕ → ℕ → ℕ → K} (hga : Gathered P0 Λ ns N rows S u1 u2 ρ Ly Q zk entry G h L x0 m) (nz : BetasNz ρ L)
    (du : UnitsH ρ ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units) (dt : TailH ρ ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units du (unitsAdd (ρ := ρ) ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans K _ _ _)).units du (x0, [])))) :
    ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ ns N) x0 du dt),
      (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ ns N) x0 du dt)) f).Holds ((closedOf P0 Λ ns N).msg m) := by
  subst hns hNn
  obtain ⟨cu, ct⟩ := claims_of_ties (closedOf P0 Λ G.ns (numsOf h)) hk4 rows b2 nz x0 du dt d1 d2 d3 d4
  obtain ⟨l, A, gL, i, Kc, l₁, l₂, jn, r1, r2, lid, cf, fs, li, hg, hz, hN, hP, h1, h2, hZ, hkr, Ap, hptM, hptD, vn,
    vi, hPt, hj, hA⟩ := hga nz du dt d1 d2 d3 d4
  exact K05_port P0 Λ hk4 rows b2 b3 S hDS hlt hNP hgs hb1 hb2 nz x0 lpW lpM lpD du dt d1 d2 d3 d4 cu ct li m entry A gL hg
    hz hN hP h1 h2 hZ hG hkr Ap hptM hptD vn vi hFit hls hlm hPt hj hA

theorem said_congr {x x' : Params.AttentionRounds} (e : x = x') {h : Heard} {G : Fork} {L : Lists}
    (s : Said x h G L) : Said x' h G L := e ▸ s

theorem tailOfP_congr {Y : Type} {T : Tail K Mg Y} {dt : TailH ρ T} {x x' : Params.AttentionRounds} (e : x = x')
    {h : Heard} {L : Lists} (s : TailOfP dt x h L) : TailOfP dt x' h L := e ▸ s

section Name
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel

/-- Q: the seat has laid (h, G); Said; and at every later ledger G' with G's slots: what stands
behind the kind (Gathered)
gives the chain's first joint's Todo. -/
def RowNameSays {St Aa Bb : Type} (P0 : OwnPar GE M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ)
    (S : Attention.Shape) (u1 u2 : UnitG) {J₂ : Type} [Fintype J₂] [DecidableEq J₂]
    (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Q : JoinLay (closedOf P0 Λ ns N)) (seat : Seat St)
    (x : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (mOf : Aa → Mg)
    (zk : Aa → Array (Array E)) (a : Aa) (b : Bb) : Prop :=
  ∃ (F G : Fork) (h : Heard) (L : Lists), seat.ledger (recA a) = some F ∧ seat.lay (recA a) h G = some (recB b) ∧
    Said x h G L ∧
    ∀ (G' : Fork) (entry : ℕ → ℕ → ℕ → GE), Stays G G' → Sized G' → G'.ns = G.ns →
      Gathered P0 Λ ns N rows S u1 u2 Reading.gl Ly Q (zk a) entry G' h L (x0 a) (mOf a) →
      ((closedOf P0 Λ ns N).own (theMeans GE _ _ _)).ch.Todo (x0 a) (mOf a)

/-- **The two laid into one**: where the written piece says yes, outside the written counts: every
gathered form worth 0, the
tables true, the join and the port's public ties, at any later ledger, give Todo. -/
theorem K05_row_name {St Aa Bb : Type} (P0 : OwnPar GE M0 X) (Λ : Lin P0 Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf (closedOf P0 Λ ns0 (numsPlan p.own k0)) rows) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (hlt : S.cf.lt = P0.D.lT) (hNP : (geoOf S).NP = (size18 P0.D).pairs)
    {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    (hG : S.G = 2 ^ S.cf.lgk) (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb)
    (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (yOf : Aa → Ex.Str) (mOf : Aa → Mg) (zk : Aa → Array (Array E))
    (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hlook : ∀ a, on a → (∀ wl, (geoOf S).single .wl = some wl → LookPts Reading.gl P0.D P0.C (P0.zOf (x0 a))
        (weights wl ((zk a).getD wl.call #[])) (inner wl ((zk a).getD wl.call #[]))) ∧
      UnitPtsM Reading.gl P0.D P0.C (P0.zOf (x0 a)) u1 ((zk a).getD u1.call #[]) ∧
      UnitPtsD Reading.gl P0.D P0.C (P0.zOf (x0 a)) u2 ((zk a).getD u2.call #[]))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns0 (numsPlan p.own k0)) J₂} {Q : JoinLay (closedOf P0 Λ ns0 (numsPlan p.own k0))} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).Leads on
      (RowNameSays P0 Λ ns0 (numsPlan p.own k0) rows S u1 u2 Ly Q seat p.own recA recB x0 mOf zk)
      (bearErr ds _ (((closedOf P0 Λ ns0 (numsPlan p.own k0)).own (theMeans GE _ _ _)).ch.eps Ex)) := by
  refine (K05_whole_any (closedOf P0 Λ ns0 (numsPlan p.own k0)) hk4 rows seat p hrec Ex ds out recA recB x0 yOf mOf on
    (fun a ha F hF => (hon a ha F hF).1) hyes hpass hd he hFit).conseq (fun _ h => h) ?_
  rintro a τ b ha _ ⟨F, G, h, L, a1, a3, c2, ⟨_, n2, n1⟩, nz, du, dt, t1, t2, t3, t4, himp⟩
  obtain ⟨_, e1, e2⟩ := hon a ha F a1
  obtain ⟨lpW, lpM, lpD⟩ := hlook a ha
  refine ⟨F, G, h, L, a1, a3, c2, fun G' entry hst zG' hns' hga => himp ?_⟩
  have c2' := said_congr hrec (c2.mono hst)
  have t2' := tailOfP_congr hrec t2
  have t1' := t1
  rw [show p.own.score = (recOf (closedOf P0 Λ ns0 (numsPlan p.own k0)) rows).score from congrArg (·.score) hrec] at t1'
  exact K05_port' P0 Λ ns0 (numsPlan p.own k0) (by rw [hns', n2, e1]) (by rw [n1, e2]) hk4 rows c2' zG' S hDS hlt hNP hgs
    hb1 hb2 hG (x0 a) lpW lpM lpD (mOf a) hFit hls hlm hga nz du dt t1' t2' t3 t4

end Name

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_row_name
#print axioms VerifiableInference.Desc.First.Att.P.K05_port'
