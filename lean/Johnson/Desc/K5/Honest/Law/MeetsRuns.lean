-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/MeetsRuns.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: THE FIRST HALVES OF WHAT THE CLAIMS SAY
(Johnson/Desc/K5/Honest/Law/SayOf.lean), FROM THE RETURNS OF THE VERIFIER's OWN FUNCTIONS AND RUNS.
Statements with their proofs. It goes on from Johnson/Desc/K5/Honest/Law/MeetsOf.lean: of that
file's premises, "every named table lies in the list" and "the indices read lie in the tables" are
drawn here from the tree's statements on these returns.

Main names:
  `plane_cases`      a plane claim that the function of the points lays is at a remainder-table
                     call, or is a softmax-table unit's
  `unit_in`          a unit has its tables and its plane claim, and the indices read lie in the
                     tables
  `planes_in`        the like at every plane claim
  `meets_of_runs`    **all six first halves**

EVERY STATEMENT IS CONDITIONAL. What `meets_of_runs` is left with, and who is meant to show each:
  the claims' values are at the shape's numbers and the lookup's key points; the verifier's function
    of the points, its function for the tables, and the runs "first" and "second" return; six
    numbers of the shape are not 0: the caller's, of a state behind the rounds.
  `AttAt`, `CellsAre`, `PtsFit`: as the head of Law/MeetsOf.lean says.
By the tree's `tabs_at` (Johnson/Desc/First/Att/Claims/TablesAt.lean), `in_tail`, `in_unit`
(Claims/InRunAll.lean), `in_five`, `in_unitLin`, `in_planeKR` (Claims/KeysIn.lean), `runs_at_old`
(Claims/EndsRun.lean), `planes_are` (Claims/PlanesAre.lean), `units_visited`, `visited_some`
(Claims/PointsRows.lean).
Limits. Nothing here says that a premise holds at any place or run.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.MeetsOf
import Johnson.Desc.K5.Honest.Law.UnitPts
import Johnson.Desc.First.Att.Claims.BackAt
import Johnson.Desc.First.Att.Claims.KeysRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (W1 RemP ScoreP ScoreT Pts Geo geoOf callOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)
open K5Law (oldOf pwBack remBack scoreBack tbBack TabsAt InTail InUnit PlaneIn MaxIn DenIn HighIn
  BitIn PosG matsOf)

/-! ## Which plane claims there are -/

/-- **A plane claim that the verifier's function of the points lays** is at a remainder-table call,
or is the plane claim of one of the softmax-table units that the function lays. -/
theorem plane_cases {g : Geo} {zk : Array (Array E)} {hh : P.Heard} {L : P.Left} {p : Pts}
    (hP : P.pointsOf g zk hh L = some p) {u : RemP} (hu : u ∈ p.planes.toList) :
    (∃ c, (c, u.call) ∈ g.calls.toList.zipIdx ∧ (c.tab == P.Tab.kr) = true) ∨
      ∃ k n, (k, n) ∈ p.scores.toList.zipIdx ∧ p.planes[k.claim]? = some u := by
  have PA := K5Law.points_are hP
  have Pl := K5Law.planes_are hP
  have nP := (K5Law.points_counts hP).2.1
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hu
  rw [Array.getElem?_toList] at hn
  have hlt : n < hh.remainders.size + hh.scores.size := by
    rcases Nat.lt_or_ge n (hh.remainders.size + hh.scores.size) with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none (by rw [nP]; exact h')] at hn
      cases hn
  rcases Nat.lt_or_ge n hh.remainders.size with h1 | h1
  · obtain ⟨r, e1⟩ : ∃ r, (g.units .kr [.rm, .rd])[n]? = some r :=
      ⟨_, List.getElem?_eq_getElem (by rw [Pl.nR]; exact h1)⟩
    have e2 := Pl.rem n _ _ e1 (Array.getElem?_eq_getElem h1)
    rw [e2] at hn
    obtain ⟨m1, m2, _⟩ := K5Law.units_mem g _ _ r (List.mem_of_getElem? e1)
    refine .inl ⟨r.2.1, ?_, m2⟩
    rw [← Option.some.inj hn]
    exact m1
  · have h2 : n - hh.remainders.size < hh.scores.size := by omega
    obtain ⟨v, e1⟩ : ∃ v, g.scores[n - hh.remainders.size]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [PA.nH]; exact h2)⟩
    obtain ⟨k, s1, c1, _⟩ := Pl.unit _ _ _ e1 (Array.getElem?_eq_getElem h2)
    refine .inr ⟨k, n - hh.remainders.size,
      List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; exact s1), ?_⟩
    rw [c1, show hh.remainders.size + (n - hh.remainders.size) = n by omega]
    exact hn

/-! ## What the runs' returns give -/

section Runs
variable {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ} {l₁ l₂ : List Aff}
  {j : JoinsP} {zk : Array (Array E)} {hh : P.Heard} {L : P.Left}

/-- **At each softmax-table unit**: it has its tables and its plane claim, and the indices that its
claims read lie in the tables. CONDITIONAL on: the claims' values are at the shape's numbers and the
lookup's key points; the function of the points and the runs "first" and "second" return; the heads
of keys and values are a power of two (public). -/
theorem unit_in (hg : i.g = geoOf S) (hz : i.zk = gL.zk)
    (hP : P.pointsOf i.g zk hh L = some i.p) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) (hG : S.G = 2 ^ S.cf.lgk) {k : ScoreP} {n : ℕ}
    (hm : (k, n) ∈ i.p.scores.toList.zipIdx) :
    ∃ tb pc, i.t.score[n]? = some tb ∧ i.p.planes[k.claim]? = some pc ∧
      PlaneIn (oldOf S gL i) (remBack pc) ∧ MaxIn (oldOf S gL i) (scoreBack k) tb.tM ∧
      InUnit (oldOf S gL i) (scoreBack k) (tbBack tb) := by
  have PA := K5Law.points_are hP
  have R := K5Law.runs_at_old (gL := gL) hg hz h1 h2
  have hk : k ∈ i.p.scores.toList := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hm)
  obtain ⟨c, hc, ht⟩ := K5Law.units_visited PA k hk
  obtain ⟨tb, pc, t1, p1⟩ := K5Law.visited_some i K _ h1 c k.call hc ht k n hm (beq_self_eq_true _)
  have et : (oldOf S gL i).t.score[n]? = some (tbBack tb) := by
    rw [K5Law.old_score, t1]
    rfl
  have ep : (oldOf S gL i).planes[(scoreBack k).claim]? = some (remBack pc) := by
    show (i.p.planes.map remBack)[k.claim]? = _
    rw [Array.getElem?_map, p1]
    rfl
  rw [hg, K5Law.calls_zip] at hc
  obtain ⟨y, hy, e⟩ := List.mem_map.1 hc
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  have hkind : (y.1.kind == Table.kfd) = true := by
    rw [← K5Law.tab_eq y.1.kind Table.kfd]
    rw [← e1] at ht
    exact ht
  have hn : (scoreBack k, n) ∈ (oldOf S gL i).scores.toList.zipIdx := by
    rw [K5Law.old_scores_zip]
    exact List.mem_map.2 ⟨(k, n), hm, rfl⟩
  have hq : ((scoreBack k).call == y.2) = true := by
    show (k.call == y.2) = true
    rw [e2]
    exact beq_self_eq_true _
  obtain ⟨a1, a2⟩ := K5Law.in_unitLin (oldOf S gL i) R.1 hy hkind hn hq et ep
  exact ⟨tb, pc, t1, p1, a1, a2, K5Law.in_unit (oldOf S gL i) R.1 hG hy hkind hn hq et⟩

/-- **At every plane claim** the indices read lie in the table. CONDITIONAL as `unit_in`. -/
theorem planes_in (hg : i.g = geoOf S) (hz : i.zk = gL.zk)
    (hP : P.pointsOf i.g zk hh L = some i.p) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) (hG : S.G = 2 ^ S.cf.lgk) :
    ∀ u ∈ i.p.planes.toList, PlaneIn (oldOf S gL i) (remBack u) := by
  intro u hu
  have R := K5Law.runs_at_old (gL := gL) hg hz h1 h2
  rcases plane_cases hP hu with ⟨c, hc, ht⟩ | ⟨k, n, hm, hp⟩
  · rw [hg, K5Law.calls_zip] at hc
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hc
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    refine K5Law.in_planeKR (oldOf S gL i) R.1 hy ?_ (pc := remBack u) ?_ ?_
    · rw [← K5Law.tab_eq y.1.kind Table.kr]
      rw [← e1] at ht
      exact ht
    · show remBack u ∈ (i.p.planes.map remBack).toList
      rw [Array.toList_map]
      exact List.mem_map.2 ⟨u, hu, rfl⟩
    · show (u.call == y.2) = true
      rw [e2]
      exact beq_self_eq_true _
  · obtain ⟨_, pc, _, p1, a1, _, _⟩ := unit_in hg hz hP h1 h2 hG hm
    rw [← Option.some.inj (p1.symm.trans hp)]
    exact a1

end Runs

/-! ## The first halves, from the returns -/

/-- **All the first halves of what the claims say**, at the claims' values i. CONDITIONAL on: the
values are at the shape's numbers and the lookup's key points; the verifier's function of the
points, its function for the tables and the runs "first" and "second" return; six numbers of the
shape are not 0 (public); `AttAt`; `CellsAre`; `PtsFit`. That the heads of keys and values are a
power of two, which the tree's statements on the runs ask, comes out of `AttAt`'s clause on the
shape. -/
theorem meets_of_runs {W : World GE} {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}
    {K : ℕ} {w : K5In} {tl : HTailF2} {M : Mats GE} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} {l₁ l₂ : List Aff} {j : JoinsP} {zk : Array (Array E)}
    {hh : P.Heard} {L : P.Left} {nW : ℕ} {lk : P.LookIn} (hg : i.g = geoOf S)
    (hz : i.zk = gL.zk) (hP : P.pointsOf i.g zk hh L = some i.p)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hpos : PosG i.g)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂)
    (A : AttAt Reading.gl W tl K M (oldOf S gL i) lid cf fs) (hc : CellsAre Reading.gl S M w)
    (F : PtsFit S lk.zx i.p) :
    MeetsPlanes W S gL i K w ∧
      (∀ k n tb, (k, n) ∈ i.p.scores.toList.zipIdx → i.t.score[n]? = some tb →
        MeetsUnit W S gL i K w k tb) ∧
      Meets5 W S gL i K w ∧ MeetsV W S gL i K w ∧ Meets7 W S gL i K w ∧ Meets8 W S gL i K w := by
  have hG : S.G = 2 ^ S.cf.lgk := (shapedG_of_hid A.shape).G
  have R := K5Law.runs_at_old (gL := gL) hg hz h1 h2
  have T : TabsAt tl (oldOf S gL i) lk.zx := K5Law.tabs_at (gL := gL) hg ht hpos
  have IT : InTail (oldOf S gL i) := K5Law.in_tail (oldOf S gL i) R.1 R.2 hG
  refine ⟨meetsPlanes_of A hc T F (planes_in hg hz hP h1 h2 hG), fun k n tb hm htb => ?_,
    meets5_of A hc T F (K5Law.in_five (oldOf S gL i) R.1) IT, meetsV_of A hc T F IT,
    meets7_of A hc T F IT, meets8_of A hc T F IT⟩
  obtain ⟨tb', _, t1, _, _, a2, a3⟩ := unit_in hg hz hP h1 h2 hG hm
  obtain rfl : tb' = tb := Option.some.inj (t1.symm.trans htb)
  have hk : i.p.scores.toList[n]? = some k := List.mem_zipIdx_iff_getElem?.1 hm
  refine meetsUnit_of A hc F (List.mem_of_getElem? hk) ?_ a2 a3
  refine UnitLaid.forall₂_at T.score n (scoreBack k) (tbBack tb') ?_ ?_
  · show (i.p.scores.map scoreBack).toList[n]? = _
    rw [Array.toList_map, List.getElem?_map, hk]
    rfl
  · rw [Array.getElem?_toList, K5Law.old_score, t1]
    rfl

end H2K5.Honest

#print axioms H2K5.Honest.plane_cases
#print axioms H2K5.Honest.unit_in
#print axioms H2K5.Honest.planes_in
#print axioms H2K5.Honest.meets_of_runs
