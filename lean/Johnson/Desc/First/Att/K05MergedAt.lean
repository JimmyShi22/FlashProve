-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MergedAt.lean: the two tests of tablesP on values (mergedPlanes,
mergedTokens, Att/TablesP.lean) pass at every record that pointsOf
makes at key points that follow the lookup's own rule (K3Pts, Att/K05LookAll.lean: the key point of
call q is a cut of zy, then zx): a key point's
last coordinates are those of zx.

Main names:
  `unit_last`: the last n coordinates of a unit's inner point are the last n of zx.
  `plane_of`: every plane claim that pointsOf lays has the inner point of a remainder unit or of a
    score unit.
  `points_div`: the four cuts of the division's record that mergedTokens reads.
  `mergedPlanes_at`, `mergedTokens_at`.

Premises: UnitsAll; K3Pts; the key points' lengths; lmS is at most a plane family's bits and at most
the length of zx; lt + ldh is at most the length
of zx; the return of pointsOf.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Merged
import Johnson.Desc.First.Att.K05ReturnsLeft
import Johnson.Desc.First.Att.K05LookAll
import Johnson.Desc.First.Att.Claims.BackAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.Part
open K5Law (remAt remOfUnit)

/-- The last n coordinates of a unit's inner point are zx's. -/
theorem unit_last {D : Dim} {C : Calls} {fam : Fam} {q : Fin 4} {u : UnitG} (I : UnitIs D C fam q u)
    {fs : Model.Forest.Shape} {zx zy : Array E} {zk : Array (Array E)} {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z)
    (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = C.a q) {n : ℕ} (hn : n ≤ fam.l D) (hx : n ≤ zx.size) :
    lastCoords (inner u (zk.getD u.call #[])) n = lastCoords zx n := by
  rw [inner_last, last_last (by rw [I.bits]; exact hn) (by rw [I.call, Kz q, I.bits]; exact I.le), I.call, H3.zk q,
    last_append _ hx]

/-- Every plane claim that pointsOf lays has the inner point of a remainder unit or of a score unit.
-/
theorem plane_of {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts} (hp : pointsOf g zk h L = some p)
    {pc : RemP} (hpc : pc ∈ p.planes.toList) :
    ∃ u, (u ∈ remainders g ∨ u ∈ g.scores) ∧ pc.z = inner u (zk.getD u.call #[]) := by
  have PA := K5Law.points_are hp
  have Pl := K5Law.planes_are hp
  have nP := (K5Law.points_counts hp).2.1
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hpc
  rw [Array.getElem?_toList] at hn
  have hlt : n < h.remainders.size + h.scores.size := by
    rcases Nat.lt_or_ge n (h.remainders.size + h.scores.size) with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none (by rw [nP]; exact h')] at hn; cases hn
  rcases Nat.lt_or_ge n h.remainders.size with h1 | h1
  · obtain ⟨r, e1⟩ : ∃ r, (g.units .kr [.rm, .rd])[n]? = some r :=
      ⟨_, List.getElem?_eq_getElem (by rw [Pl.nR]; exact h1)⟩
    have e2 := Pl.rem n _ _ e1 (Array.getElem?_eq_getElem h1)
    rw [e2] at hn
    refine ⟨g.unitAt r.1 r.2.1 r.2.2, .inl (List.mem_map.2 ⟨_, List.mem_of_getElem? e1, rfl⟩), ?_⟩
    rw [← Option.some.inj hn]
    rfl
  · have h2 : n - h.remainders.size < h.scores.size := by omega
    obtain ⟨u, e1⟩ : ∃ u, g.scores[n - h.remainders.size]? = some u :=
      ⟨_, List.getElem?_eq_getElem (by rw [PA.nH]; exact h2)⟩
    obtain ⟨k, _, c1, c2, _⟩ := Pl.unit _ _ _ e1 (Array.getElem?_eq_getElem h2)
    rw [c1, show h.remainders.size + (n - h.remainders.size) = n by omega, hn] at c2
    refine ⟨u, .inr (List.mem_of_getElem? e1), ?_⟩
    rw [Option.some.inj c2]
    rfl

/-- The four cuts that mergedTokens reads. -/
theorem points_div {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts} (hp : pointsOf g zk h L = some p) :
    ∃ uW uH, g.single .wl = some uW ∧ g.single .wh = some uH ∧
      p.d.ziW = (inner uW (zk.getD uW.call #[])).extract (1 + g.lgk) (1 + g.lgk + g.lt) ∧
      p.d.zcW = (inner uW (zk.getD uW.call #[])).extract (1 + g.lgk + g.lt) (1 + g.lgk + g.lt + g.ldh) ∧
      p.d.ziH = (inner uH (zk.getD uH.call #[])).extract g.lgk (g.lgk + g.lt) ∧
      p.d.zcH = (inner uH (zk.getD uH.call #[])).extract (g.lgk + g.lt) (g.lgk + g.lt + g.ldh) := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, _, _, uW, hW, _, _, uH, hH, _, _, _, _, e⟩ := hp
  subst e
  exact ⟨uW, uH, hW, hH, rfl, rfl, rfl, rfl⟩

section At
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {r1 r2 u1 u2 wl ix wh : UnitG}

theorem mergedPlanes_at (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) {zx zy : Array E} {zk : Array (Array E)}
    {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z) (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q)
    (hl : ∀ f : Fam, Cb.Pv.Att.End.IsPlane f → S.cf.lmS ≤ f.l (dimOf S)) (hx : S.cf.lmS ≤ zx.size)
    {h : Heard} {L : Left} {p : Pts} (hp : pointsOf (geoOf S) zk h L = some p) :
    mergedPlanes (geoOf S).lmS zx p.planes = true := by
  unfold mergedPlanes
  rw [Array.all_eq_true_iff_forall_mem]
  intro pc hpc
  obtain ⟨u, hu, e⟩ := plane_of hp (Array.mem_toList_iff.2 hpc)
  rw [e, beq_iff_eq]
  rw [U.rem, U.sco] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with (rfl | rfl) | (rfl | rfl)
  · exact unit_last U.m1 H3 Kz (hl .m1 trivial) hx
  · exact unit_last U.d1 H3 Kz (hl .d1 trivial) hx
  · exact unit_last U.m2 H3 Kz (hl .m2 trivial) hx
  · exact unit_last U.d2 H3 Kz (hl .d2 trivial) hx

theorem mergedTokens_at (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT)
    {zx zy : Array E} {zk : Array (Array E)}
    {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z) (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q)
    (hx : S.cf.lt + S.cf.ldh ≤ zx.size)
    {h : Heard} {L : Left} {p : Pts} (hp : pointsOf (geoOf S) zk h L = some p) :
    mergedTokens (geoOf S) zx p.d = true := by
  obtain ⟨_, _, i3, _, i5⟩ := inner_lens U N hl Kz
  obtain ⟨uW, uH, sW, sH, e1, e2, e3, e4⟩ := points_div hp
  obtain rfl : wl = uW := Option.some.inj (U.sWl.symm.trans sW)
  obtain rfl : wh = uH := Option.some.inj (U.sWh.symm.trans sH)
  have hlt := N.lt
  have a1 : p.d.ziW ++ p.d.zcW = lastCoords zx (S.cf.lt + S.cf.ldh) := by
    rw [e1, e2, extract_glue _ (by omega) (by omega), ← unit_last U.w3 H3 Kz (n := S.cf.lt + S.cf.ldh) (by
      show _ ≤ 1 + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh
      omega) hx]
    unfold lastCoords
    rw [i3]
    show _ = (inner wl (zk.getD wl.call #[])).extract _ _
    congr 1
    · show 1 + S.cf.lgk = _
      omega
  have a2 : p.d.ziH ++ p.d.zcH = lastCoords zx (S.cf.lt + S.cf.ldh) := by
    rw [e3, e4, extract_glue _ (by omega) (by omega), ← unit_last U.f4 H3 Kz (n := S.cf.lt + S.cf.ldh) (by
      show _ ≤ S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh
      omega) hx]
    unfold lastCoords
    rw [i5]
    show _ = (inner wh (zk.getD wh.call #[])).extract _ _
    congr 1
    · show S.cf.lgk = _
      omega
  unfold mergedTokens
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨a1.trans a2.symm, a1⟩

end At

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.mergedPlanes_at
#print axioms VerifiableInference.Desc.First.Att.P.mergedTokens_at
