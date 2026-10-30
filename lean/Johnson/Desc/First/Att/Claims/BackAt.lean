-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/BackAt.lean: kind K5: six_say and say_tail_at (Claims/PortMine.lean)
the other way round, at a record of the kind's own whose
place has two remainder-table units and two softmax-table units, where pointsOf, "first" and
"second" have returned.

Main names:
  `sayAt_back`: the six are there, with their public facts (InTail, InUnit): no claim's worth is
    asked for that; and what the claims say of the six
    and of the tail gives "every gathered form is worth 0" (AllZero (l₁ ++ l₂)).

That pointsOf lays as many plane claims as there are remainder messages and units, so that there are
no others, is points_counts
(Claims/Place.lean).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Place

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Left Pts CallG Keys UnitG ScoreP RemP geoOf callOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {S : Attention.Shape} {gL : Forest.Heard}
  {i : P.Runs.In} {K : ℕ} {l₁ l₂ : List Aff} {j : JoinsP}

/-- **The six with their public facts; and from what the claims say to «every gathered form is worth
0».** -/
theorem sayAt_back (A : Plan) {zk : Array (Array E)} {hh : P.Heard} {L : P.Left}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (hP : P.pointsOf i.g zk hh L = some i.p)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂) (hG : S.G = 2 ^ S.cf.lgk)
    {r1 r2 : ℕ × CallG × Keys} (hkr : i.g.units .kr [.rm, .rd] = [r1, r2])
    {u1 u2 : UnitG} (hgs : i.g.scores = [u1, u2]) :
    ∃ a1 a2 k1 k2, hh.remainders[0]? = some a1 ∧ hh.remainders[1]? = some a2 ∧
      i.p.scores[0]? = some k1 ∧ i.p.scores[1]? = some k2 ∧ InTail (oldOf S gL i) ∧
      InUnit (oldOf S gL i) (scoreBack k1) ((oldOf S gL i).t.score.getD 0 default) ∧
      InUnit (oldOf S gL i) (scoreBack k2) ((oldOf S gL i).t.score.getD 1 default) ∧
      (PlanesSay ρ W (oldOf S gL i) K (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2).pM →
        PlanesSay ρ W (oldOf S gL i) K (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2).pD →
        UnitAt ρ W (oldOf S gL i) K (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2).kM ((oldOf S gL i).t.score.getD 0 default)
          (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2).cM →
        UnitAt ρ W (oldOf S gL i) K (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2).kD ((oldOf S gL i).t.score.getD 1 default)
          (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2).cD →
        Say5 ρ W (oldOf S gL i) K → Say6 ρ W (oldOf S gL i) K → Say7 ρ W (oldOf S gL i) K →
        Say8 ρ W (oldOf S gL i) K → AllZero ρ W (l₁ ++ l₂)) := by
  have PA := points_are hP
  have Pl := planes_are hP
  have hv := units_visited PA
  have R := runs_at_old (gL := gL) hg hz h1 h2
  have nR : hh.remainders.size = 2 := by rw [← Pl.nR, hkr]; rfl
  have nH : hh.scores.size = 2 := by rw [← PA.nH, hgs]; rfl
  have nP : i.p.planes.size = 4 := by rw [(points_counts hP).2.1, nR, nH]
  have nS : i.p.scores.size = 2 := by
    have e := congrArg List.length (s0_are PA)
    simp only [List.length_map, Array.length_toList] at e
    rw [e, nH]
  have ea1 : hh.remainders[0]? = some hh.remainders[0] := Array.getElem?_eq_getElem (by omega)
  have ea2 : hh.remainders[1]? = some hh.remainders[1] := Array.getElem?_eq_getElem (by omega)
  have eo1 : hh.scores[0]? = some hh.scores[0] := Array.getElem?_eq_getElem (by omega)
  have eo2 : hh.scores[1]? = some hh.scores[1] := Array.getElem?_eq_getElem (by omega)
  have p1 := Pl.rem 0 r1 _ (by rw [hkr]; rfl) ea1
  have p2 := Pl.rem 1 r2 _ (by rw [hkr]; rfl) ea2
  obtain ⟨k1, s1, q1, c1, z1, _, _, _⟩ := Pl.unit 0 u1 _ (by rw [hgs]; rfl) eo1
  obtain ⟨k2, s2, q2, c2, z2, _, _, _⟩ := Pl.unit 1 u2 _ (by rw [hgs]; rfl) eo2
  rw [← z1] at c1
  rw [← z2] at c2
  have hs : ∀ x ∈ i.p.scores.toList.zipIdx, ∃ tb pc, i.t.score[x.2]? = some tb ∧
      i.p.planes[x.1.claim]? = some pc := by
    intro x hx
    obtain ⟨c, hc, ht⟩ := hv x.1 (List.mem_zipIdx_iff_getElem?.1 hx |> fun e => List.mem_of_getElem? e)
    exact visited_some i K _ h1 c x.1.call hc ht x.1 x.2 hx (beq_self_eq_true _)
  have unitPub : ∀ (n : ℕ) (k : ScoreP), i.p.scores[n]? = some k →
      ∃ tb, i.t.score[n]? = some tb ∧ (oldOf S gL i).t.score.getD n default = tbBack tb ∧
        InUnit (oldOf S gL i) (scoreBack k) ((oldOf S gL i).t.score.getD n default) := by
    intro n k hk
    have hm : (k, n) ∈ i.p.scores.toList.zipIdx :=
      List.mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; exact hk)
    obtain ⟨tb, _, t1, _⟩ := hs (k, n) hm
    have et : (oldOf S gL i).t.score[n]? = some (tbBack tb) := by rw [old_score, t1]; rfl
    have eg : (oldOf S gL i).t.score.getD n default = tbBack tb := by
      rw [Array.getD_eq_getD_getElem?, et]
      rfl
    refine ⟨tb, t1, eg, ?_⟩
    rw [eg]
    obtain ⟨c', hc', ht⟩ := hv k (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk))
    rw [hg, calls_zip] at hc'
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hc'
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    refine in_unit (oldOf S gL i) R.1 hG (c := y.1) (q := y.2) hy ?_ (k := scoreBack k) (n := n) ?_ ?_ et
    · rw [← tab_eq y.1.kind Table.kfd]
      rw [← e1] at ht
      exact ht
    · rw [old_scores_zip]
      exact List.mem_map.2 ⟨(k, n), hm, rfl⟩
    · show (k.call == y.2) = true
      rw [e2]
      exact beq_self_eq_true _
  obtain ⟨tb1, t1, g1, I1⟩ := unitPub 0 k1 s1
  obtain ⟨tb2, t2, g2, I2⟩ := unitPub 1 k2 s2
  refine ⟨_, _, k1, k2, ea1, ea2, s1, s2, in_tail (oldOf S gL i) R.1 R.2 hG, I1, I2,
    fun sM sD U1 U2 s5 s6 s7 s8 => ?_⟩
  refine (say_at Kf ρ W A S gL i K l₁ l₂ j hg hz hN hv h1 h2).2 ⟨?_, ?_, s5, s6, s7, s8⟩
  · intro y _ _ pc hpc _
    have hpc' : pc ∈ (i.p.planes.map remBack).toList := hpc
    rw [Array.toList_map] at hpc'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hpc'
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hq
    rw [Array.getElem?_toList] at hn
    have hn4 : n < 4 := by
      rcases Nat.lt_or_ge n 4 with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none (by rw [nP]; exact h')] at hn; cases hn
    rw [q1, nR] at c1
    rw [q2, nR] at c2
    interval_cases n
    · rw [p1] at hn
      rw [← Option.some.inj hn]
      exact sM
    · rw [p2] at hn
      rw [← Option.some.inj hn]
      exact sD
    · rw [c1] at hn
      rw [← Option.some.inj hn]
      exact U1.planes
    · rw [c2] at hn
      rw [← Option.some.inj hn]
      exact U2.planes
  · intro x hx
    have hx' := List.mem_zipIdx_iff_getElem?.1 hx
    rw [Array.getElem?_toList] at hx'
    have hn2 : x.2 < 2 := by
      rcases Nat.lt_or_ge x.2 2 with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none (by rw [nS]; exact h')] at hx'; cases hx'
    obtain ⟨k, n⟩ := x
    have hn2' : n < 2 := hn2
    have hx'' : i.p.scores[n]? = some k := hx'
    interval_cases n
    · rw [s1] at hx''
      obtain rfl := Option.some.inj hx''
      refine ⟨tb1, _, t1, c1, ?_⟩
      rw [← g1]
      exact U1
    · rw [s2] at hx''
      obtain rfl := Option.some.inj hx''
      refine ⟨tb2, _, t2, c2, ?_⟩
      rw [← g2]
      exact U2

end K5Law

#print axioms K5Law.sayAt_back
