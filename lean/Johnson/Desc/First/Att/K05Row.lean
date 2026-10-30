-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Row.lean: Att/K05Cap.lean's theorem with Att/K05Join.lean's laid behind
it.

Main names:
  `closed_tailSeam`, `closed_unitsSeam`: the join's two premises on the letters, at the closed
    parameters and the
    library's numberings: lemmas.
  `weights_size`, `pieces_size`, `cnt_two`: the claims' record counts, at each unit, twice the
    unit's pieces.
  `RowSays`, `row_core`, `K05_row`: from decide's yes, at the parameters made of the plan, at every
    later ledger
    G': as K05_cap; and, for every l that leftP returns there, where SayAt holds in the world of the
      message's own
    mask (by say_at, under its own premises: every form that the runs "first" and "second" gather is
      worth 0), at
    a record whose numbers are the shape's and whose points are pointsOf's of h and l (PointsAre):
      (1) the proved chain's last claim on the run holds
    exactly if Dn, the letters' linear claims (TailLin, UnitsLin), and for each sumcheck that owes
      its output
    claims: each end value's typed map at the output's point is what its written reader's form is
      worth
    (EndsMean, UnitsMeans); (2) the letter owF, which TailLin holds (what the score at the index
      owes), holds
    exactly if for every pair the typed first map at the output's point is what the written reader's
      form is
    worth.

Premises left: K05_cap's · S.NP is the description's number of pairs.
Limits. SayAt is a premise at a free record: whoever spends it from "every gathered form is worth 0"
brings
Att/Claims/SayAt.lean's own premises. What a reader's form means for the message (EndsMean,
UnitsMeans, and the right
side of (2)), and the letters' other linear claims against the lists' linear group, are not shown in
this file or in what it imports.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Cap
import Johnson.Desc.First.Att.K05Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf sc3Num sc3Num_lt scdNum scdNum_lt ownTrs)
open VerifiableInference.Desc.Part
open K5Law (SayAt PointsAre unitReader endsE endsV endsK endsH oldOf sum3Back tail_rows tail_ends)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}

/-- **TailSeam at the closed parameters.** -/
theorem closed_tailSeam (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C
      (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (hz : Sized G)
    (nz : BetasNz ρ L) (x1 : Seen K X) (m : Mg) :
    TailSeam (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own Mn).tail L h nz (landedTail _ Mn) x1)
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h (Λ.maskOf m) m := by
  obtain ⟨cE, cM, cVD, _, cH⟩ := closed_ends P0 Λ rows hs hz m
  exact ⟨fun y => sc3Num_lt y, cE, fun y => sc3Num_lt y, cM, fun y => sc3Num_lt y, cVD,
    fun y => scdNum_lt (size18 P0.D) y,
    fun y => closed_c18 P0 Λ G.ns (numsOf h) m y (le_of_lt (put_lt hz (end_put hs.sD (scdNum_lt (size18 P0.D) y)))),
    fun y => sc3Num_lt y, cH⟩

/-- **UnitsSeam at the closed parameters**, where the claims' record counts as many end values at
each unit as the plan. -/
theorem closed_unitsSeam (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C
      (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (hz : Sized G) (x0 : X)
    (m : Mg) (cnt : ℕ → ℕ) (c0 : cnt 0 = 2 * P0.D.nb) (c1 : cnt 1 = 2 * P0.D.nb) :
    UnitsSeam ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units
      (unitsAdd (ρ := ρ) ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units (landedUnits _ Mn) L.planes.flatten L.units
        (x0, []))
      (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList cnt 0 (Λ.maskOf m) m := by
  obtain ⟨o1, o2, v1, H1, v2, H2, hos, _, ⟨_, _, a3, _⟩, ⟨_, _, b3, _⟩⟩ := units_two hs.units
  have e1 : (numsOf h).endOf .s6b = o1.2.sEnd := by
    unfold Nums.endOf Nums.uEnd numsOf
    simp [hos]
  have e2 : (numsOf h).endOf .s6d = o2.2.sEnd := by
    unfold Nums.endOf Nums.uEnd numsOf
    simp [hos]
  rw [hos]
  refine ⟨fun y => by rw [c0]; exact sc3Num_lt y, le_of_eq c0, fun y => ?_,
    fun y => by rw [c1]; exact sc3Num_lt y, le_of_eq c1, fun y => ?_, trivial⟩
  · have := closed_c P0 Λ G.ns (numsOf h) m .s6b y (by
      rw [e1]
      exact le_of_lt (put_lt hz (end_put a3 (sc3Num_lt y))))
    rw [e1] at this
    exact this
  · have := closed_c P0 Λ G.ns (numsOf h) m .s6d y (by
      rw [e2]
      exact le_of_lt (put_lt hz (end_put b3 (sc3Num_lt y))))
    rw [e2] at this
    exact this

/-! ## The claims' record's counts -/

theorem weights_size (u : UnitG) (zk : Array E) : (weights u zk).size = u.pcs.length := by
  unfold weights
  simp [List.length_mergeSort]

theorem pieces_size (u : UnitG) (zk : Array E) : (piecesOf u zk).size = u.pcs.length := by
  unfold piecesOf
  simp [List.length_mergeSort]

/-- The claims' record counts, at each of two units, twice the unit's pieces. -/
theorem cnt_two {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left} (H : PointsAre i.g zk h l i.p)
    {u1 u2 : UnitG} (hg : i.g.scores = [u1, u2]) {o1 o2 : ℕ × MaskedSum.Heard} (ho : h.scores.toList = [o1, o2])
    {f1 f2 : Aff} (hf : l.scores.toList = [f1, f2]) :
    cntOf i 0 = 2 * (weights u1 (zk.getD u1.call #[])).size ∧
      cntOf i 1 = 2 * (weights u2 (zk.getD u2.call #[])).size := by
  have hs := H.units
  have e : ((i.g.scores.toArray.zip h.scores).zip l.scores).toList = [((u1, o1), f1), ((u2, o2), f2)] := by
    rw [Array.toList_zip, Array.toList_zip, ho, hf, hg]
    rfl
  rw [e] at hs
  have hsc : ∀ n, i.p.scores[n]? = i.p.scores.toList[n]? := fun n => (Array.getElem?_toList).symm
  unfold cntOf
  rw [hsc 0, hsc 1]
  generalize i.p.scores.toList = ks at hs ⊢
  rcases hs with _ | ⟨⟨⟨_, _, _, a1⟩, _⟩, hs⟩
  rcases hs with _ | ⟨⟨⟨_, _, _, a2⟩, _⟩, hs⟩
  cases hs
  constructor
  · show 2 * _ = _
    simp only [List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [a1, pieces_size, weights_size]
  · show 2 * _ = _
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some]
    rw [a2, pieces_size, weights_size]

/-- What the capstone with the join behind it says of parameters P. -/
def RowSays {Mg : Type} (P : OwnPar K Mg X) (maskOf : Mg → ℕ → K) (x : Params.AttentionRounds) (F G : Fork)
    (rs : List Fmt.RoundView) (h : Heard) (S : Attention.Shape) (zk : Array (Array E))
    (Pts : Reading K → X → Prop) : Prop :=
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
          UnitsAreP (P.own (theMeans K P.D P.C P.kap)).units du h.scores.toList ∧ TailIsP dt x h L) ∧
        (UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) ∧
          dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) ∧
        (∀ (Ex : ExtSpec) (y : Ex.Str), ((P.own (theMeans K P.D P.C P.kap)).ch.R Ex).red.out (x0, y)
          ((P.own (theMeans K P.D P.C P.kap)).ch.join Ex (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt)) =
          some ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt), y)) ∧
        ∀ (l : Left), leftP (geoOf S) zk h G = some l →
        ∀ (Dn : X → Mg → Prop) (m : Mg) (entry : ℕ → ℕ → ℕ → K) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ),
          i.g = geoOf S → PointsAre i.g zk h l i.p → SayAt ρ (G.worldOf ρ (maskOf m) entry) S gL i Kc →
          ((P.own (theMeans K P.D P.C P.kap)).ch.Last Dn
              ((P.own (theMeans K P.D P.C P.kap)).ch.run x0 (ownTrs (P.own (theMeans K P.D P.C P.kap)) du dt)) m ↔
            Dn x0 m ∧
              (UnitsLin (P.own (theMeans K P.D P.C P.kap)).units du (x0, []) m ∧
                UnitsMeans (P.own (theMeans K P.D P.C P.kap)).units du
                  (unitsAdd (ρ := ρ) (P.own (theMeans K P.D P.C P.kap)).units (landedUnits P _) L.planes.flatten
                    L.units (x0, [])) 0 (unitReader S gL i Kc) (G.worldOf ρ (maskOf m) entry) m) ∧
              (TailLin dt (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])) m ∧
                EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sE dt.dE
                  (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aE
                  (endsE (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sVM dt.dVM
                  (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aM
                  (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpm) i.t.tVM i.t.ptM false i.t.qVM)
                  (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sVD dt.dVD
                  (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aVD
                  (endsV (oldOf S gL i) Kc (sum3Back i.p.d.vpd) i.t.tVD i.t.ptD true i.t.qVD)
                  (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sD dt.dD
                  (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aD
                  (endsK (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m ∧
                EndsMean (P.own (theMeans K P.D P.C P.kap)).tail.sH dt.dH
                  (tailAdd (P.own (theMeans K P.D P.C P.kap)).tail L h nz (landedTail P _)
                    (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))).aH
                  (endsH (oldOf S gL i) Kc) (G.worldOf ρ (maskOf m) entry) m)) ∧
          ((P.tail (theMeans K P.D P.C P.kap)).toTail.owF
              (dt.dF.nx (dt.x6 (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])))) m ↔
            ∀ b : Fin P.D.nb, P.sF.T.map dt.dF.st (P.msg m) (b, false)
              (ldPartIni P.sF.T.nv P.sF.T.deg (pDummy K P.sF.T.DY) dt.dF.out.pt) =
                (_root_.Fo.readHeadT (oldOf S gL i) Kc i.t.qF S.atQ ((oldOf S gL i).x.rg S) ((oldOf S gL i).x.rc S)
                  (b.1 / S.HA) (b.1 % S.HA)).value ρ (G.worldOf ρ (maskOf m) entry))

/-- The capstone with the join behind it, at the parameters read off what was heard. -/
theorem row_core (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {F G G' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hk4 : P0.kap = 4) (rows : ℕ)
    (hh : hear (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows) (F, rs, 0) = some (h, G, [], 0)) (hzF : Sized F)
    (hst : Stays G G') (hz' : Sized G')
    (S : Attention.Shape) (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S)
    (hlt : S.cf.lt = P0.D.lT) (hNP : (geoOf S).NP = (size18 P0.D).pairs) (hNP2 : S.NP = P0.D.nb) {u1 u2 : UnitG}
    (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    {zk : Array (Array E)} :
    RowSays (closedOf P0 Λ G'.ns (numsOf h)) Λ.maskOf (recOf (closedOf P0 Λ G'.ns (numsOf h)) rows) F G' rs h S zk
      (LookAll P0 S zk u1 u2) := by
  obtain ⟨L, c1, c2, c3, c4, c5⟩ := cap_core P0 Λ (theMeans K _ _ _) hk4 rows hh hzF hst hz' S hDS Z hlt hNP hgs hb1 hb2
    (zk := zk)
  refine ⟨L, c1, c2, c3, c4, fun ρ nz x0 hp => ?_⟩
  obtain ⟨du, dt, ⟨d1, d2, d3, d4, dq⟩, ⟨d5, d6⟩, d7, d8, d9⟩ := c5 ρ nz x0 hp.1 hp.2.1 hp.2.2
  refine ⟨du, dt, ⟨d1, d2, d3, d4, d5, d6⟩, d7, d8, fun l hl Dn m entry gL i Kc hig H Sy => ?_⟩
  have li := leftP_spec hl
  refine ⟨?_, ?_⟩
  · obtain ⟨o1, o2, _, _, _, _, hos, _, _, _⟩ := units_two c2.units
    obtain ⟨f1, f2, hfs, _, _⟩ := scores_two li hgs hos
    obtain ⟨k0, k1⟩ := cnt_two H (by rw [hig]; exact hgs) hos hfs
    rw [hp.2.1.nPw] at k0
    rw [hp.2.2.nPw] at k1
    refine (d9 l li Dn m entry).trans (and_congr_right' ?_)
    exact K05_join _ du dt c2 d1 d2 _ _ d3 d4 (Λ.maskOf m) entry m H Sy hNP2 (by
        show S.Lam = P0.D.nl
        rw [hDS]
        rfl) hlt
      (closed_unitsSeam P0 Λ (theMeans K _ _ _) rows c2 c3 x0 m (cntOf i) k0 k1)
      (closed_tailSeam P0 Λ (theMeans K _ _ _) rows c2 c3 nz _ m) _ _
  · subst dq
    obtain ⟨wl, _, _, _, _, _, _, lF, _, _⟩ := li.rest
    have hsl := (tail_ends H Sy).2.2.2.1
    rw [hNP2] at hsl
    exact value_owF_paid (closedOf P0 Λ G'.ns (numsOf h)) (theMeans K _ _ _) rows c2 nz (landedTail _ _) (fun _ => rfl) _
      (geoOf S) hlt (by
        show (geoOf S).lgk = P0.D.lg
        rw [hDS]
        rfl) d2 (Λ.maskOf m) entry m lF
      (fun j => closed_kF P0 Λ G'.ns (numsOf h) m j (le_of_lt (put_lt c3 (c2.pM j.1 (by rw [c2.lM]; exact j.2)))))
      (fun b => by
        have := (closed_ends P0 Λ rows c2 c3 m).2.2.2.1 (b, false)
        simpa [sc3Num] using this)
      (D1_at ((closedOf P0 Λ G'.ns (numsOf h)).tail (theMeans K _ _ _)).toTail.sF _ d2.zF c2.sF (Λ.maskOf m) entry m
        fun j => closed_w P0 Λ G'.ns (numsOf h) m .s16 j (le_of_lt (put_lt c3
          (coef_put ((closedOf P0 Λ G'.ns (numsOf h)).tail (theMeans K _ _ _)).toTail.sF d2.zF c2.sF j))))
      (fun b => _root_.Fo.readHeadT (oldOf S gL i) Kc i.t.qF S.atQ ((oldOf S gL i).x.rg S) ((oldOf S gL i).x.rc S)
        (b / S.HA) (b % S.HA))
      (tail_rows H Sy).2.2.2.1 hsl _

/-- **K05_cap with K05_join behind it.** -/
theorem K05_row (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {St : Type} (seat : Seat St) (p : Par) (s s' : St)
    (rs : List Fmt.RoundView) (hd : decide seat p s rs = .ok s') (hz : ∀ F, seat.ledger s = some F → Sized F)
    (hk4 : P0.kap = 4) (rows : ℕ) (hrec : p.own = recOf P0 rows) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) (hNP2 : S.NP = P0.D.nb) {u1 u2 : UnitG}
    (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false) (zk : Array (Array E)) :
    ∃ (F G : Fork) (h : Heard), seat.ledger s = some F ∧ seat.lay s h G = some s' ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧
      ∀ G', Stays G G' → G'.ns = G.ns → Sized G' →
        RowSays (closedOf P0 Λ F.ns (numsPlan p.own F.next)) Λ.maskOf p.own F G' rs h S zk
          (LookAll P0 S zk u1 u2) := by
  obtain ⟨_, F, h, G, a1, a2, a3⟩ := (decide_lays seat p s s' rs).1 hd
  refine ⟨F, G, h, a1, a3, a2, fun G' hst hns hz' => ?_⟩
  have e := closed_is_plan P0 Λ a2 (hz F a1) G' hns
  rw [← e]
  rw [hrec] at a2 ⊢
  exact row_core P0 Λ hk4 rows a2 (hz F a1) hst hz' S hDS Z hlt hNP hNP2 hgs hb1 hb2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_row
#print axioms VerifiableInference.Desc.First.Att.P.closed_unitsSeam
#print axioms VerifiableInference.Desc.First.Att.P.closed_tailSeam
