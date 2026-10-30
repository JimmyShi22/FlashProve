-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05UnitsAll.lean: at the closed parameters: K05_law's premise UnitsPrem,
whole, drawn out
of Said.

Main names:
  `units_two`: two units have been heard: their records and lists, named.
  `closed_unitsPrem`: from Said, UnitsOfP, the values' tie at the library's numbering, scoreW's and
    left's
    returns at each unit, the first unit below the diagonal and the second on it, UnitPtsM and
      UnitPtsD.

Sources: what Att/K05Units.lean names.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Units

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH UnitsH SameRead recOf sc3Num)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 X : Type}

/-- Two units have been heard. -/
theorem units_two {p1 p2 : ℕ × ℕ} {os : List (ℕ × MaskedSum.Heard)} {pre : List E} {l : List (List E × PscH)}
    {G : Fork} (h : UnitsAt [p1, p2] os pre l G) :
    ∃ o1 o2 v1 H1 v2 H2, os = [o1, o2] ∧ l = [(v1, H1), (v2, H2)] ∧
      (v1.length = 7 ∧ PutRun G o1.1 v1 ∧ SumAt (.slot (o1.1 + 6)) (products p1.1 p1.2) (pre ++ v1) H1 o1.2 G ∧
        SameRead o1.2.target (v1.getD 6 zeroE)) ∧
      (v2.length = 7 ∧ PutRun G o2.1 v2 ∧ SumAt (.slot (o2.1 + 6)) (products p2.1 p2.2) ([] ++ v2) H2 o2.2 G ∧
        SameRead o2.2.target (v2.getD 6 zeroE)) := by
  rcases os with _ | ⟨o1, os⟩
  · cases l <;> simp [UnitsAt] at h
  rcases l with _ | ⟨⟨v1, H1⟩, l⟩
  · simp [UnitsAt] at h
  obtain ⟨a1, a2, a3, a4, h⟩ := h
  rcases os with _ | ⟨o2, os⟩
  · cases l <;> simp [UnitsAt] at h
  rcases l with _ | ⟨⟨v2, H2⟩, l⟩
  · simp [UnitsAt] at h
  obtain ⟨b1, b2, b3, b4, h⟩ := h
  rcases os with _ | ⟨o3, os⟩
  · rcases l with _ | ⟨x, l⟩
    · exact ⟨o1, o2, v1, H1, v2, H2, rfl, rfl, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
    · simp [UnitsAt] at h
  · cases l <;> simp [UnitsAt] at h

/-- **UnitsPrem at the closed parameters, from Said.** -/
theorem closed_unitsPrem (P0 : OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg) {h : Heard} {G : Fork}
    (Mn : Means K (closedOf P0 Λ G.ns (numsOf h)).D (closedOf P0 Λ G.ns (numsOf h)).C (closedOf P0 Λ G.ns (numsOf h)).kap)
    (rows : ℕ) {L : Lists} (hs : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (hz : Sized G)
    (du : UnitsH ρ ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units)
    (hu : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score
      h.scores.toList L.planes.flatten L.units)
    (um : UnitsNums ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units)
    (hu1 : ∀ a : Fin P0.D.nb × Bool, um.1 a = sc3Num a) (hu2 : ∀ a : Fin P0.D.nb × Bool, um.2.1 a = sc3Num a) (x0 : X)
    (hv : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du
      (unitsAdd (ρ := ρ) ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units um L.planes.flatten L.units (x0, [])))
    {g : Geo} (g2 : g.lgk = P0.D.lg) (g3 : g.lnT = P0.D.lP + 1) {u1 u2 : UnitG} {zk1 zk2 : Array E} {f1 f2 : Aff}
    (hb1 : u1.below = true) (hb2 : u2.below = false)
    (hw1 : ∀ o, h.scores.toList[0]? = some o → ∃ Wt, scoreW g u1 zk1 (chal o.2) = some Wt ∧ left G o.2 Wt = some f1)
    (hw2 : ∀ o, h.scores.toList[1]? = some o → ∃ Wt, scoreW g u2 zk2 (chal o.2) = some Wt ∧ left G o.2 Wt = some f2)
    (lp1 : UnitPtsM ρ P0.D P0.C (P0.zOf x0) u1 zk1) (lp2 : UnitPtsD ρ P0.D P0.C (P0.zOf x0) u2 zk2)
    (entry : ℕ → ℕ → ℕ → K) (m : Mg) :
    UnitsPrem ((closedOf P0 Λ G.ns (numsOf h)).own Mn).units du h.scores.toList [f1, f2] (G.worldOf ρ (Λ.maskOf m) entry) m := by
  obtain ⟨o1, o2, v1, H1, v2, H2, hos, hl, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := units_two hs.units
  obtain ⟨W1, w1, l1⟩ := hw1 o1 (by rw [hos]; rfl)
  obtain ⟨W2, w2, l2⟩ := hw2 o2 (by rw [hos]; rfl)
  rw [hos, hl] at hu
  rw [hl] at hv
  rw [hos]
  obtain ⟨z1, of1, z2, of2, _⟩ := hu
  obtain ⟨⟨v11, s11⟩, ⟨v21, s21⟩, _⟩ := hv
  refine ⟨closed_unitM_prem P0 Λ hos hz du.1 z1 of1 a3 a1 a2 a4 (fun a => ?_) hb1 w1 ?_ g2 g3 entry m l1,
    closed_unitD_prem P0 Λ hos hz du.2.1 z2 of2 b3 b1 b2 b4 (fun a => ?_) hb2 w2 ?_ g2 g3 entry m l2, trivial⟩
  · rw [v11 a, of1.H]
    exact congrArg (fun j => ρ.val (H1.v.getD j zeroE)) (hu1 a)
  · rw [s11]
    exact lp1
  · rw [v21 a, of2.H]
    exact congrArg (fun j => ρ.val (H2.v.getD j zeroE)) (hu2 a)
  · rw [s21]
    exact lp2

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_unitsPrem
