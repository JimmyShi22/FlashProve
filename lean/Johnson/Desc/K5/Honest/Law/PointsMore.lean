-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PointsMore.lean: small statements on the two relations "the same
challenges in the parts in front of part q" (SameTo, Johnson/Desc/K5/Honest/Law/HeardIs.lean) and
"the fields made of the key points alone are the same" (KeySame,
Johnson/Desc/K5/Honest/Law/PointsIs.lean), with their proofs; and the prover's values at two lists
of named points that are so related. No frame of a prover is imported.

  SameTo.trans   the relation goes through a third value heard
  key_plane, key_unit   KeySame by a plane claim's, a unit's, number
  zcAt_same .. rhp2At_same, accAt_same, ibAt_same   the lone values of the division
  unitA_same, unitB_same, vmA_same, vmB_same, vdA_same, vdB_same   the two maps of the sumchecks
                 of products, at a point r that is handed in

Limits. Every statement is conditional on the relation, or on the one part of KeySame that it reads
(divKey, unitKey); vmB_same and vdB_same also on: the two batching elements are the same, which is
no matter of the key points. Equations of the program's elements, word for word. No property is
claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.StableKey
import Johnson.Desc.K5.Honest.Law.TilesKit
import Johnson.Desc.K5.Honest.Law.ReadVM
import Johnson.Desc.K5.Honest.Law.ReadVD

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc.First.Att.P (Geo Heard Pts RemP ScoreP DivP chal scoreTiles pointM
  pointD)

/-- The relation on what was heard goes through a third value. -/
theorem SameTo.trans {x : OnBytes.Params.AttentionRounds} {q : Nat} {a b c : Heard}
    (h1 : SameTo x q a b) (h2 : SameTo x q b c) : SameTo x q a c :=
  { nR := h1.nR.trans h2.nR
    nS := h1.nS.trans h2.nS
    scores := fun i hi u v hu hv => by
      have hlt : i < b.scores.size := by
        rw [← h1.nS]
        rcases Nat.lt_or_ge i a.scores.size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hu
          cases hu
      have hm : b.scores[i]? = some b.scores[i] := Array.getElem?_eq_getElem hlt
      exact (h1.scores i hi u _ hu hm).trans (h2.scores i hi _ v hm hv)
    division := fun h => (h1.division h).trans (h2.division h)
    gam := fun h => (h1.gam h).trans (h2.gam h)
    below := fun h => (h1.below h).trans (h2.below h)
    on := fun h => (h1.on h).trans (h2.on h)
    point := fun h => (h1.point h).trans (h2.point h)
    om := fun h => (h1.om h).trans (h2.om h)
    atIndex := fun h => (h1.atIndex h).trans (h2.atIndex h)
    om' := fun h => (h1.om' h).trans (h2.om' h)
    key := fun h => (h1.key h).trans (h2.key h)
    om'' := fun h => (h1.om'' h).trans (h2.om'' h)
    cells := fun h => (h1.cells h).trans (h2.cells h) }

/-- KeySame by a plane claim's number. -/
theorem key_plane {p p' : Pts} (K : KeySame p p') (n : Nat) :
    (p.planes[n]?).map remKey = (p'.planes[n]?).map remKey := by
  have h := congrArg (fun l => l[n]?) K.planes
  simp only [List.getElem?_map, Array.getElem?_toList] at h
  exact h

/-- KeySame by a unit's number. -/
theorem key_unit {p p' : Pts} (K : KeySame p p') (n : Nat) :
    (p.scores[n]?).map unitKey = (p'.scores[n]?).map unitKey := by
  have h := congrArg (fun l => l[n]?) K.scores
  simp only [List.getElem?_map, Array.getElem?_toList] at h
  exact h

section
variable (g : Geo) (w : K5In) {d d' : DivP} (h : divKey d = divKey d')
include h

theorem accAt_same : accAt g w d = accAt g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _, _, _, _, e6, e7, e8, _⟩ := h
  unfold accAt
  rw [e1, e6, e7, e8]

theorem zcAt_same : zcAt g w d = zcAt g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _, _, _, _, e6, e7, _⟩ := h
  unfold zcAt
  rw [e1, e6, e7]

theorem rhAt_same : rhAt g w d = rhAt g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _, _, _, _, e6, e7, e8, _⟩ := h
  unfold rhAt
  rw [e1, e6, e7, e8]

theorem rhpAt_same : rhpAt g w d = rhpAt g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _, _, _, _, e6, e7, e8, _⟩ := h
  unfold rhpAt
  rw [e1, e6, e7, e8]

theorem ibAt_same : ibAt g w d = ibAt g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨_, e2, _, _, _, _, _, _, e9, e10, _⟩ := h
  unfold ibAt
  rw [e2, e9, e10]

theorem rh2At_same : rh2At g w d = rh2At g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨_, _, e3, _, _, _, _, _, _, _, e11, e12, e13⟩ := h
  unfold rh2At
  rw [e3, e11, e12, e13]

theorem rhp2At_same : rhp2At g w d = rhp2At g w d' := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨_, _, e3, _, _, _, _, _, _, _, e11, e12, e13⟩ := h
  unfold rhp2At
  rw [e3, e11, e12, e13]

theorem vmA_same (r : Array E) (b : Nat) : vmA g w d r b = vmA g w d' r b := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _, _, _, _, _, e7, _⟩ := h
  simp only [vmA, belowAt, pointM, DivP.zilo]
  rw [e1, e7]

theorem vmB_same (hg : d.gam = d'.gam) (ec r : Array E) (b : Nat) :
    vmB g w d ec r b = vmB g w d' ec r b := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _⟩ := h
  simp only [vmB, belowAt]
  rw [e1, hg]

theorem vdA_same (r : Array E) (b : Nat) : vdA g w d r b = vdA g w d' r b := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _, _, _, _, _, e7, _⟩ := h
  simp only [vdA, pointD, DivP.zilo]
  rw [e1, e7]

theorem vdB_same (hg : d.gam = d'.gam) (ec r : Array E) (b : Nat) :
    vdB g w d ec r b = vdB g w d' ec r b := by
  simp only [divKey, Prod.mk.injEq] at h
  obtain ⟨e1, _⟩ := h
  simp only [vdB]
  rw [e1, hg]

end

section
variable (g : Geo) (w : K5In) {k k' : ScoreP} (h : unitKey k = unitKey k')
include h

theorem unitA_same (r : Array E) (b : Nat) : unitA g w k r b = unitA g w k' r b := by
  simp only [unitKey, Prod.mk.injEq] at h
  obtain ⟨_, _, e3, e4, _, _, e7, _, _⟩ := h
  simp only [unitA, scoreTiles]
  rw [e3, e4, e7]

theorem unitB_same (r : Array E) (b : Nat) : unitB g w k r b = unitB g w k' r b := by
  simp only [unitKey, Prod.mk.injEq] at h
  obtain ⟨_, _, e3, e4, _, _, _, e8, _⟩ := h
  simp only [unitB, scoreTiles]
  rw [e3, e4, e8]

end

end H2K5.Honest

#print axioms H2K5.Honest.SameTo.trans
#print axioms H2K5.Honest.key_plane
#print axioms H2K5.Honest.key_unit
#print axioms H2K5.Honest.accAt_same
#print axioms H2K5.Honest.zcAt_same
#print axioms H2K5.Honest.rhAt_same
#print axioms H2K5.Honest.rhpAt_same
#print axioms H2K5.Honest.ibAt_same
#print axioms H2K5.Honest.rh2At_same
#print axioms H2K5.Honest.rhp2At_same
#print axioms H2K5.Honest.vmA_same
#print axioms H2K5.Honest.vmB_same
#print axioms H2K5.Honest.vdA_same
#print axioms H2K5.Honest.vdB_same
#print axioms H2K5.Honest.unitA_same
#print axioms H2K5.Honest.unitB_same
