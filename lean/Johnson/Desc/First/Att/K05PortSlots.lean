-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PortSlots.lean: the record SlotsH of Att/Claims/PortAll.lean (the
dictionary of slots, 17 fields) at the
closed parameters and the run made of what was heard.

Main names:
  `slotsH_at`: SlotsH in the world of the message's own mask, at the record oldOf S gL i of
    OnBytes/Model and the six records
    sixAt, for all values of the late entries.

How: slot_at_landed (Att/K05SlotAt.lean), with UnitsAreP and TailIsP by units_areP and tail_isP;
slotsH_of
(Att/Claims/PortMine.lean) at the numbers of numsOf h; the eight equations of Att/K05Run.lean on the
outputs.
Premises: Said; Sized; the sizes are the shape's; two plane messages; the four ties; the letters'
claims; PointsAre; AttPub;
the places of the two remainder-table units' slots and of the two softmax-table units' records.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Port
import Johnson.Desc.First.Att.K05SlotAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (partHearLaw)
open K5Law (oldOf PointsAre sixAt SlotsH slotsH_of)
open OnBytes.Road.Rows (AttPub)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 Mg X : Type}

theorem slotsH_at (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (rows : ℕ) {L : Lists}
    (b2 : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (b3 : Sized G) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (hnpl : P0.npl = 2) (nz : BetasNz ρ L) (x0 : X)
    (du : UnitsH ρ ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units) (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du
      (unitsAdd (ρ := ρ) ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, []))))
    (cu : UnitsClaims ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])) (ct : dt.Claims (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])))
    (m : Mg) (entry : ℕ → ℕ → ℕ → K) (gL : Forest.Heard) {i : Runs.In} {zk : Array (Array E)} {l : Left}
    (PA : PointsAre i.g zk h l i.p) {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (Ap : AttPub ρ (oldOf S gL i) lid cf fs) {r1 r2 : ℕ × CallG × Keys} {u1 u2 : UnitG} {a1 a2 : ℕ} {k1 k2 : ScoreP}
    (ha1 : h.remainders[0]? = some a1) (ha2 : h.remainders[1]? = some a2) (hk1 : i.p.scores[0]? = some k1)
    (hk2 : i.p.scores[1]? = some k2) {J₂ : Type} (ul : J₂ → K) :
    SlotsH (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) (closedOf P0 Λ G.ns (numsOf h)) (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt) m
      (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2) ul := by
  have iu := units_areP partHearLaw ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du _ _ _ _ b2.units d1
  have it := tail_isP partHearLaw dt b2 d2
  have Sa := slot_at_landed P0 Λ G.ns (numsOf h) rfl rfl (theMeans K _ _ _) rows b2 b3 nz entry m _ _ du dt d1 d2 d3 d4 iu it
  obtain ⟨o1, o2, _, _, _, _, hos, _, _, _⟩ := units_two b2.units
  have ho1 : h.scores[0]? = some o1 := by rw [← Array.getElem?_toList, hos]; rfl
  have ho2 : h.scores[1]? = some o2 := by rw [← Array.getElem?_toList, hos]; rfl
  have p0 : (numsOf h).plane 0 = a1 := by
    show h.remainders.toList.getD 0 0 = a1
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ha1]
    rfl
  have p1 : (numsOf h).plane 1 = a2 := by
    show h.remainders.toList.getD 1 0 = a2
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ha2]
    rfl
  have s0 : (numsOf h).seven 0 = o1.1 := by
    show ((((h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd))[0]?).map (·.1)).getD 0) = _
    rw [hos]
    rfl
  have s1 : (numsOf h).seven 1 = o2.1 := by
    show ((((h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd))[1]?).map (·.1)).getD 0) = _
    rw [hos]
    rfl
  have e0 : (numsOf h).uEnd 0 = o1.2.sEnd := by
    show ((((h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd))[0]?).map (·.2.2)).getD 0) = _
    rw [hos]
    rfl
  have e1 : (numsOf h).uEnd 1 = o2.2.sEnd := by
    show ((((h.scores.toList.map fun o => (o.1, o.2.first, o.2.sEnd))[1]?).map (·.2.2)).getD 0) = _
    rw [hos]
    rfl
  exact slotsH_of (Pp := (closedOf P0 Λ G.ns (numsOf h))) (u := runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt) (m := m) (ul := ul)
    (W := G.worldOf ρ (Λ.maskOf m) entry) PA hDS Ap hnpl hk1 hk2 ho1 ho2 (numsOf h).plane (numsOf h).seven (numsOf h).uEnd p0 p1 s0 s1 e0 e1
    Sa.rM Sa.rD Sa.rE Sa.rV Sa.rF
    (fun y => by rw [run_oM _ x0 du dt cu]; exact Sa.eUM _ ul y)
    (fun y => by rw [run_oD _ x0 du dt cu]; exact Sa.eUD _ ul y)
    (fun y => by rw [run_oE _ x0 du dt ct]; exact Sa.eE _ ul y)
    (fun y => by rw [run_oVM _ x0 du dt ct]; exact Sa.eVM _ ul y)
    (fun y => by rw [run_oVD _ x0 du dt ct]; exact Sa.eVD _ ul y)
    (fun y => by rw [run_oF _ x0 du dt ct]; exact Sa.eF _ ul y)
    (fun y => by rw [run_oK _ x0 du dt ct]; exact Sa.eK _ ul y)
    (fun y => by rw [run_oH _ x0 du dt ct]; exact Sa.eH _ ul y)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.slotsH_at
