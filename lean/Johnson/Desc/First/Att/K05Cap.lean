-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Cap.lean: K05_law at the closed parameters, with no premise on a row left.

Main names:
  `landedUnits`, `landedTail`: the library's numberings of the end values.
  `cap_core`: where the hearing has returned, at a ledger G' in which what is filled has stayed (the
    claims are
    gathered behind other kinds' steps): at closedOf P0 Λ G'.ns (numsOf h): for every
    reading at which no beta reads 0 and every first statement: there are data made of what was
      heard (their
    ties are said, and which data the tail's are), the letters' claims hold of them, the reduction
      puts out the chain's run on them, and for
    every l that leftP returns on G' and every message, in the world of its own mask, the chain's
      last claim on
    the run holds exactly if Dn and the kind's bill at the rows l. The data do not hang on leftP.
  `CapSays`, `LookAll`, `K05_cap`: from decide's yes (the hearing's return is said too), at closedOf
    P0 Λ F.ns (numsPlan p.own F.next): parameters
    made of the plan and of two numbers of the ledger in front of the hearing, so fixed before the
      rounds; at
    the library's own four equations (theMeans), the letters of ownAt_knowAt.

Paid inside: the part's three laws (Part/MaskedSumTie.lean) · the letters' numbers and claims ·
(D1), (D2), (D4) of
the sumchecks.
Premises left: kap = 4 · p.own = recOf P0 rows · P0.D = L5.dimOf S · Sizes S · two equations of
numbers · the
place has two units, the first below the diagonal, the second on it · LookAll (the lookup's points)
· BetasNz ·
Sized in front and at G' · Stays and the number of slots along the later steps. P0's and Λ's fields
stay
parameters.
Limits. Where leftP refuses the last clause is idle. That the premises on public numbers hold
together at a
shape that the planner returns is not shown in this file or in what it imports. Of the bill's rows
seven come through
UnitsPrem and TailPrem; the score at the index's stands inside owF (Att/K05OwF.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05TailAll
import Johnson.Desc.First.Att.K05UnitsAll
import Johnson.Desc.First.Att.K05Paid
import Johnson.Desc.First.Att.K05Numbers
import Cb.Pv.Att.OwnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf sc3Num scdNum ownTrs own_out ownAt_fits)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (partHearLaw partRowLaw)

variable {K : Type} [Field K] [Fintype K] {M0 X : Type}

/-- The library's numberings of the end values. -/
def landedUnits (P : OwnPar K M0 X) (Mn : Means K P.D P.C P.kap) : UnitsNums (P.own Mn).units :=
  (fun a : Fin P.D.nb × Bool => sc3Num a, fun a : Fin P.D.nb × Bool => sc3Num a, ())

def landedTail (P : OwnPar K M0 X) (Mn : Means K P.D P.C P.kap) : TailNums (P.tail Mn).toTail :=
  ⟨fun a : Fin P.D.nb × Bool => sc3Num a, fun a : Fin P.D.nb × Bool => sc3Num a,
    fun a : Fin P.D.nb × Bool => sc3Num a, fun a : Fin P.D.nb × Bool => sc3Num a,
    fun a : (size18 P.D).A => scdNum (size18 P.D) a, fun a : Fin P.D.nb × Bool => sc3Num a⟩

/-- leftP's clause on the units, where the place has two units and two have been heard. -/
theorem scores_two {g : Geo} {zk : Array (Array E)} {h : Heard} {G : Fork} {l : Left} (li : LeftIs g zk h G l)
    {u1 u2 : UnitG} (hg : g.scores = [u1, u2]) {o1 o2 : ℕ × MaskedSum.Heard} (ho : h.scores.toList = [o1, o2]) :
    ∃ f1 f2, l.scores.toList = [f1, f2] ∧ ScoresLeft g zk G (u1, o1) f1 ∧ ScoresLeft g zk G (u2, o2) f2 := by
  have hs := li.scores
  have e : (g.scores.toArray.zip h.scores).toList = [(u1, o1), (u2, o2)] := by
    rw [Array.toList_zip, ho, hg]
    rfl
  rw [e] at hs
  generalize l.scores.toList = fs at hs ⊢
  rcases hs with _ | ⟨a1, hs⟩
  rcases hs with _ | ⟨a2, hs⟩
  cases hs
  exact ⟨_, _, rfl, a1, a2⟩

/-- **K05_law at the closed parameters, with no premise on a row left.** -/
theorem cap_core (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {F G G' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (Mn : Means K (closedOf P0 Λ G'.ns (numsOf h)).D (closedOf P0 Λ G'.ns (numsOf h)).C
      (closedOf P0 Λ G'.ns (numsOf h)).kap)
    (hk4 : P0.kap = 4) (rows : ℕ)
    (hh : hear (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows) (F, rs, 0) = some (h, G, [], 0)) (hzF : Sized F)
    (hst : Stays G G') (hz' : Sized G')
    (S : Attention.Shape) (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S)
    (hlt : S.cf.lt = P0.D.lT) (hNP : (geoOf S).NP = (size18 P0.D).pairs) {u1 u2 : UnitG}
    (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    {zk : Array (Array E)} :
    ∃ L : Lists, RoundsAre L.rounds rs ∧ Said (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows) h G' L ∧ Sized G' ∧
      Stays F G' ∧
      ∀ (ρ : Reading K) (nz : BetasNz ρ L) (x0 : X),
        (∀ wl, (geoOf S).single .wl = some wl → LookPts ρ P0.D P0.C (P0.zOf x0)
          (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[]))) →
        UnitPtsM ρ P0.D P0.C (P0.zOf x0) u1 (zk.getD u1.call #[]) →
        UnitPtsD ρ P0.D P0.C (P0.zOf x0) u2 (zk.getD u2.call #[]) →
        ∃ (du : UnitsH ρ ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units)
          (dt : TailH ρ ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).tail),
          (UnitsOfP ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du
              (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units ∧
            TailOfP dt (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows) h L ∧
            UnitsVals ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du
              (unitsAdd (ρ := ρ) ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units (landedUnits _ Mn) L.planes.flatten
                L.units (x0, [])) ∧
            TailVals dt (tailAdd ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).tail L h nz (landedTail _ Mn)
              (seenAfter ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []))) ∧
            dt = tailData ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).tail L h nz (landedTail _ Mn)
              (seenAfter ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []))) ∧
          (UnitsAreP ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du h.scores.toList ∧
            TailIsP dt (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows) h L) ∧
          (UnitsClaims ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []) ∧
            dt.Claims (seenAfter ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []))) ∧
          (∀ (Ex : ExtSpec) (y : Ex.Str), (((closedOf P0 Λ G'.ns (numsOf h)).own Mn).ch.R Ex).red.out (x0, y)
            (((closedOf P0 Λ G'.ns (numsOf h)).own Mn).ch.join Ex
              (ownTrs ((closedOf P0 Λ G'.ns (numsOf h)).own Mn) du dt)) =
            some (((closedOf P0 Λ G'.ns (numsOf h)).own Mn).ch.run x0
              (ownTrs ((closedOf P0 Λ G'.ns (numsOf h)).own Mn) du dt), y)) ∧
          ∀ (l : Left), LeftIs (geoOf S) zk h G' l → ∀ (Dn : X → Mg → Prop) (m : Mg) (entry : ℕ → ℕ → ℕ → K),
            (((closedOf P0 Λ G'.ns (numsOf h)).own Mn).ch.Last Dn
                (((closedOf P0 Λ G'.ns (numsOf h)).own Mn).ch.run x0
                  (ownTrs ((closedOf P0 Λ G'.ns (numsOf h)).own Mn) du dt)) m ↔
              Dn x0 m ∧
                UnitsBill ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []) l.scores.toList
                  (G'.worldOf ρ (Λ.maskOf m) entry) m ∧
                TailBill dt (seenAfter ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, [])) l
                  (G'.worldOf ρ (Λ.maskOf m) entry) m) := by
  obtain ⟨L, b1, b0, _, b4, b5⟩ := hear_law_paid hh hzF
  have b2 := b0.mono hst
  have b3 := hz'
  refine ⟨L, b1, b2, b3, b4.trans hst, ?_⟩
  intro ρ nz x0 lpW lpM lpD
  have hl := Z.lnT
  have g2 : (geoOf S).lgk = P0.D.lg := by rw [hDS]; rfl
  have g3 : (geoOf S).lnT = P0.D.lP + 1 := by
    rw [hDS]
    show S.lnT = S.lnT - 1 + 1
    omega
  have hne : (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows).score ≠ [] := by simp [recOf]
  obtain ⟨fu, ft⟩ := fits_of_own ((closedOf P0 Λ G'.ns (numsOf h)).own Mn) _
    (ownAt_fits (closedOf P0 Λ G'.ns (numsOf h)) Mn hk4 rows) hne
  rw [← b2.nPlanes, ← planes_length b2.planes] at fu
  obtain ⟨du, d1, d3⟩ := units_exist ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units _ _ _ _ b2.units fu nz.units
    (unitsAdd (ρ := ρ) ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units (landedUnits _ Mn) L.planes.flatten L.units
      (x0, []))
  obtain ⟨e1, e2⟩ := tail_exists ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).tail b2 hne nz ft
    (tailAdd ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).tail L h nz (landedTail _ Mn)
      (seenAfter ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, [])))
  have cu : UnitsClaims ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []) :=
    (units_claims _ du _ _ _ _ (landedUnits _ Mn) _ d1 d3).2
      (units_targets_of_last _ du _ _ _ _ _ (last_own _ Mn) b2.units d1)
  have ct := (tail_claims ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).tail L h nz (landedTail _ Mn)
    (seenAfter ((closedOf P0 Λ G'.ns (numsOf h)).own Mn).units du (x0, []))).2
      (value_tail_targets (closedOf P0 Λ G'.ns (numsOf h)) Mn rows b2 nz (landedTail _ Mn) (fun i => by
        simp [landedTail, sc3Num]) _)
  obtain ⟨o1, o2, _, _, _, _, hos, _, _, _⟩ := units_two b2.units
  refine ⟨du, _, ⟨d1, e1, d3, e2, rfl⟩, b5 K ρ Mg X _ du _ d1 e1, ⟨cu, ct⟩, fun Ex y => own_out _ du _ Ex x0 y,
    fun l li Dn m entry => ?_⟩
  obtain ⟨f1, f2, hfs, ⟨W1, w1, l1⟩, ⟨W2, w2, l2⟩⟩ := scores_two li hgs hos
  refine k5_last partRowLaw ((closedOf P0 Λ G'.ns (numsOf h)).own Mn) du _ b2 d1 e1 Dn x0 m cu ct ?_
    (closed_tailPrem P0 Λ Mn hk4 rows b2 b3 nz (landedTail _ Mn) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) _ S hDS Z hlt hNP e1 li lpW entry m)
  rw [hfs]
  exact closed_unitsPrem P0 Λ Mn rows b2 b3 du d1 (landedUnits _ Mn) (fun _ => rfl) (fun _ => rfl) x0 d3 g2 g3 hb1 hb2
    (fun o ho => by
      rw [hos] at ho
      obtain rfl : o1 = o := Option.some.inj ho
      exact ⟨W1, w1, l1⟩)
    (fun o ho => by
      rw [hos] at ho
      obtain rfl : o2 = o := Option.some.inj ho
      exact ⟨W2, w2, l2⟩) lpM lpD entry m

/-! ## At the parameters made of the plan, from decide's yes -/

/-- What the capstone says of parameters P (the letters are P.own at the library's own four
equations). Pts: the lookup's
points' premises, at a reading and a first statement. -/
def CapSays {Mg : Type} (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (IsLeft : Left → Prop) (Pts : Reading K → X → Prop) : Prop :=
  ∃ L : Lists, RoundsAre L.rounds rs ∧ Said x h G L ∧ Sized G ∧ Stays F G ∧
    ∀ (ρ : Reading K) (nz : BetasNz ρ L) (x0 : X), Pts ρ x0 →
      ∃ (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units)
        (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail),
        (UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du x.score h.scores.toList L.planes.flatten L.units ∧
          TailOfP dt x h L ∧
          UnitsVals (P.own (theMeans K P.D P.C P.kap)).units du
            (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten L.units
              (x0, [])) ∧
          TailVals dt (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
            (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) ∧
          dt = tailData (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
            (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) ∧
        (UnitsAreP (P.own (theMeans K P.D P.C P.kap)).units du h.scores.toList ∧ TailIsP dt x h L) ∧
        (UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) ∧
          dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) ∧
        (∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex).red.out (x0, y)
          ((P.own (theMeans K P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt)) =
          some ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt), y)) ∧
        ∀ (l : Left), IsLeft l → ∀ (Dn : X → Mg → Prop) (m : Mg) (entry : ℕ → ℕ → ℕ → K),
          ((P.own (theMeans K P.D P.C P.kap)).ch.Last Dn
              ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt)) m ↔
            Dn x0 m ∧
              UnitsBill (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) l.scores.toList
                (G.worldOf ρ (maskOf m) entry) m ∧
              TailBill dt (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])) l
                (G.worldOf ρ (maskOf m) entry) m)

/-- The lookup's points' premises, together. -/
def LookAll (P0 : OwnPar K M0 X) (S : Attention.Shape) (zk : Array (Array E)) (u1 u2 : UnitG) (ρ : Reading K) (x0 : X) :
    Prop :=
  (∀ wl, (geoOf S).single .wl = some wl → LookPts ρ P0.D P0.C (P0.zOf x0)
    (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[]))) ∧
  UnitPtsM ρ P0.D P0.C (P0.zOf x0) u1 (zk.getD u1.call #[]) ∧
  UnitPtsD ρ P0.D P0.C (P0.zOf x0) u2 (zk.getD u2.call #[])

/-- **From decide's yes.** At the parameters made of the plan and of two numbers of the ledger in
front (so: fixed before the
rounds): CapSays, at every later ledger G' in which what is filled has stayed, with as many slots
and its arrays' lengths (the
claims are gathered behind other kinds' steps); the data do not hang on leftP; the last clause
speaks of every l that leftP
returns there. -/
theorem K05_cap (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {St : Type} (seat : Seat St) (p : Par) (s s' : St)
    (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s') (hz : ∀ F, seat.ledger s = some F → Sized F)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf P0 rows) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2])
    (hb1 : u1.below = true) (hb2 : u2.below = false) (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        CapSays (closedOf P0 Λ F.ns (numsPlan p.own F.next)) Λ.maskOf p.own F G' rs h
          (fun l => leftP (geoOf S) zk h G' = some l) (LookAll P0 S zk u1 u2) := by
  obtain ⟨_, F, h, G, a1, a2, a3⟩ := (decide_lays seat p s s' rs).1 hd
  refine ⟨F, G, h, a1, a3, a2, fun G' hst hns hz' => ?_⟩
  have e := closed_is_plan P0 Λ a2 (hz F a1) G' hns
  rw [← e]
  rw [hrec] at a2 ⊢
  obtain ⟨L, c1, c2, c3, c4, c5⟩ := cap_core P0 Λ (theMeans K _ _ _) hk4 rows a2 (hz F a1) hst hz' S hDS Z hlt hNP hgs hb1 hb2
    (zk := zk)
  refine ⟨L, c1, c2, c3, c4, fun ρ nz x0 hp => ?_⟩
  obtain ⟨du, dt, d1, d2, d3, d4, d5⟩ := c5 ρ nz x0 hp.1 hp.2.1 hp.2.2
  exact ⟨du, dt, d1, d2, d3, d4, fun l hl => d5 l (leftP_spec hl)⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_cap
#print axioms VerifiableInference.Desc.First.Att.P.cap_core
