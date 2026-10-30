-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Rows.lean: the eight rows. At the closed parameters, for all typed data
with the four ties: each row
that leftP leaves is worth 0 in the ledger's world of the message's mask exactly if the library's
row claim UHolds holds
of the matching output of the run made of what was heard.

Main names:
  `prem_uholds`: RowPrem gives "the row is worth 0 iff UHolds".
  `Rows8`, `rows_core`.

Premises of rows_core: Said; Sized; public numbers of the shape; the lookup's points (LookPts,
UnitPtsM, UnitPtsD); the four
ties; the letters' claims; LeftIs. It calls the lemmas that K05_cap calls (closed_unitsPrem,
closed_tailPrem) and
closed_atIndex_prem; the data are brought to the made ones by tailH_one.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Run
import Johnson.Desc.First.Att.K05Cap
import Johnson.Desc.First.Att.K05ClosedAt
import Johnson.Desc.First.Att.K05One

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf sc3Num scdNum ownTrs ownAt_fits)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (partRowLaw)

variable {K : Type} [Field K] [Fintype K] {M0 X : Type} {ρ : Reading K}

theorem prem_uholds {M Y : Type} (S : SumL K M Y) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf)
    {W : World K} {m : M} {f : Aff} (p : RowPrem S D C hh f W m) :
    f.value ρ W = 0 ↔ S.T.our.par.UHolds D.out (S.msg m) := by
  obtain ⟨S0, e, D1, D2, D4⟩ := p
  subst e
  exact row_uholds partRowLaw S D hs hD h W S0 m D1 D2 D4

/-- The eight equivalences. -/
structure Rows8 {Mg : Type} (P : OwnPar K Mg X) (u : P.Run) (f1 f2 : Aff) (l : Left) (W : World K) (m : Mg) : Prop where
  rM : f1.value ρ W = 0 ↔ P.uM.T.our.par.UHolds u.oM (P.msg m)
  rD : f2.value ρ W = 0 ↔ P.uD.T.our.par.UHolds u.oD (P.msg m)
  rE : l.division.value ρ W = 0 ↔ P.sE.T.our.par.UHolds u.oE (P.msg m)
  rVM : l.below.value ρ W = 0 ↔ P.sVM.T.our.par.UHolds u.oVM (P.msg m)
  rVD : l.on.value ρ W = 0 ↔ P.sVD.T.our.par.UHolds u.oVD (P.msg m)
  rF : l.atIndex.value ρ W = 0 ↔ P.sF.T.our.par.UHolds u.oF (P.msg m)
  rK : l.key.value ρ W = 0 ↔ P.sD.T.our.par.UHolds u.oK (P.msg m)
  rH : l.cells.value ρ W = 0 ↔ P.sH.T.our.par.UHolds u.oH (P.msg m)

/-- **The eight rows.** -/
theorem rows_core (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (hk4 : P0.kap = 4)
    (rows : ℕ) {L : Lists} (b2 : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (b3 : Sized G) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (Z : OnBytes.Road.Rows.Sizes S) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2])
    (hb1 : u1.below = true) (hb2 : u2.below = false) {zk : Array (Array E)} (nz : BetasNz ρ L) (x0 : X)
    (lpW : ∀ wl, (geoOf S).single .wl = some wl → LookPts ρ P0.D P0.C (P0.zOf x0)
      (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])))
    (lpM : UnitPtsM ρ P0.D P0.C (P0.zOf x0) u1 (zk.getD u1.call #[]))
    (lpD : UnitPtsD ρ P0.D P0.C (P0.zOf x0) u2 (zk.getD u2.call #[]))
    (du : UnitsH ρ ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units) (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du
      (unitsAdd (ρ := ρ) ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, []))))
    (cu : UnitsClaims ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])) (ct : dt.Claims (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])))
    {l : Left} (li : LeftIs (geoOf S) zk h G l) (m : Mg) (entry : ℕ → ℕ → ℕ → K) :
    ∃ f1 f2, l.scores.toList = [f1, f2] ∧
      Rows8 (ρ := ρ) (closedOf P0 Λ G.ns (numsOf h)) (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt) f1 f2 l (G.worldOf ρ (Λ.maskOf m) entry) m := by
  have g1 : (geoOf S).lt = P0.D.lT := hlt
  have g2 : (geoOf S).lgk = P0.D.lg := by rw [hDS]; rfl
  have hl := Z.lnT
  have g3 : (geoOf S).lnT = P0.D.lP + 1 := by
    rw [hDS]
    show S.lnT = S.lnT - 1 + 1
    omega
  have hne : (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score ≠ [] := by simp [recOf]
  obtain ⟨_, ft⟩ := fits_of_own ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)) _ (ownAt_fits (closedOf P0 Λ G.ns (numsOf h)) _ hk4 rows) hne
  obtain ⟨e1, e2⟩ := tail_exists ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail b2 hne nz ft
    (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])))
  obtain rfl : dt = tailData ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])) :=
    tailH_one d2 e1 d4 e2
  obtain ⟨o1, o2, v1, H1, v2, H2, hos, hlu, ⟨_, _, a3, _⟩, ⟨_, _, a3', _⟩⟩ := units_two b2.units
  obtain ⟨f1, f2, hfs, ⟨W1, w1, l1⟩, ⟨W2, w2, l2⟩⟩ := scores_two li hgs hos
  have pt := closed_tailPrem P0 Λ (theMeans K _ _ _) hk4 rows b2 b3 nz (landedTail _ _) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ S hDS Z hlt hNP e1 li lpW entry m
  have pu := closed_unitsPrem P0 Λ (theMeans K _ _ _) rows b2 b3 du d1 (landedUnits _ _) (fun _ => rfl) (fun _ => rfl)
    x0 d3 g2 g3 hb1 hb2
    (fun o ho => by
      rw [hos] at ho
      obtain rfl : o1 = o := Option.some.inj ho
      exact ⟨W1, w1, l1⟩)
    (fun o ho => by
      rw [hos] at ho
      obtain rfl : o2 = o := Option.some.inj ho
      exact ⟨W2, w2, l2⟩) lpM lpD entry m
  obtain ⟨_, _, _, _, _, _, _, lF, _, _⟩ := li.rest
  have pF := closed_atIndex_prem P0 Λ (theMeans K _ _ _) rows b2 b3 nz (landedTail _ _) (fun _ => rfl)
    (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])) (geoOf S) g1 g2 e1 entry m lF
  rw [hos] at pu
  obtain ⟨q1, q2, _⟩ := pu
  have d1' := d1
  rw [hos, hlu] at d1'
  obtain ⟨z1, of1, z2, of2, _⟩ := d1'
  refine ⟨f1, f2, hfs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [run_oM _ x0 du _ cu]
    exact prem_uholds _ du.1 z1 of1 a3 q1
  · rw [run_oD _ x0 du _ cu]
    exact prem_uholds _ du.2.1 z2 of2 a3' q2
  · rw [run_oE _ x0 du _ ct]
    exact prem_uholds _ _ e1.zE e1.oE b2.sE pt.pE
  · rw [run_oVM _ x0 du _ ct]
    exact prem_uholds _ _ e1.zM e1.oM b2.sM pt.pM
  · rw [run_oVD _ x0 du _ ct]
    exact prem_uholds _ _ e1.zVD e1.oVD b2.sVD pt.pVD
  · rw [run_oF _ x0 du _ ct]
    exact prem_uholds _ _ e1.zF e1.oF b2.sF pF
  · rw [run_oK _ x0 du _ ct]
    exact prem_uholds _ _ e1.zD e1.oD b2.sD pt.pD
  · rw [run_oH _ x0 du _ ct]
    exact prem_uholds _ _ e1.zH e1.oH b2.sH pt.pH

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.rows_core
