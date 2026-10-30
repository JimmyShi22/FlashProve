-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5TabsEnd.lean: AT AN ATTENTION SEGMENT's NUMBERS THE END OF THE SMALLNESS TEST's TABLES IS AT MOST THE LENGTH THAT THE PLAN GIVES THE THIRD VECTOR OF READS (Attention.Shape.tableElems). GENERAL IN THE SHAPE S AND IN i: no scope, no head, no numeral, no divisibility. A join of lemmas.

"The tables' end": P5J.K8N.tabsEnd (Johnson/P5J/K8ThreeBoxes.lean): the first entry behind the last table of K8.tabs.
THE STONES, FROM OTHER FILES: the end is the sum of the families' entries (OnBytes.Road.K4.Plan.end_sum0 · famSum, Johnson/Road/K4/Plan/TabsEndSum.lean) · at each of the five sorts of matrix a table has at most its written entries, and of the segments fm and fd a call holds at most as many as it has segments (VerifiableInference.Desc.K9Asks.att_tab_as | _ah | _ao | _bA | _qa · held_le, Johnson/Desc/First/Link/Law/AttTabEntries.lean, general in the map over the list of matrices) · getD_k | getD_m (Johnson/P5J/K8ThreeBoxes.lean).
OF THIS FILE:
  `markQ_m`, `markQ_k`: the library's Fo.PlaneMat.markQ keeps a matrix's rows and columns: so the five are had at φ := markQ.
  `famSum_le`: a family each of whose tables has at most B entries.
  `att_units_le`: the units that K8.Asks.attention counts are at most the count in Shape.tableElems.
  **`att_tabsEnd_le`**: see its statement.
WHY IT HOLDS: family by family k · (m / len) is at most the matching term of tableElems. It is tight at the release's sizes (by an evaluation) because there everything divides: not shown here.
Limits. An inequality on numbers. That any plan has these numbers is not said here. Nothing on soundness.

-/
import Johnson.P5J.K8ThreeBoxes
import Johnson.Road.K4.Plan.TabsEndSum
import Johnson.Desc.First.Link.Law.AttTabEntries
import Johnson.Desc.First.K8.Asks
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (K8.Par K8.layFamily K8.Asks.attention)
open VerifiableInference.Desc.K9Asks (att_tab_as att_tab_ah att_tab_ao att_tab_bA att_tab_qa held_le)
open OnBytes.Road.K4.Plan (famSum end_sum0 sum_rep)

theorem markQ_m (M : TMat) : (Fo.PlaneMat.markQ M).m = M.m := by
  unfold Fo.PlaneMat.markQ
  split <;> rfl

theorem markQ_k (M : TMat) : (Fo.PlaneMat.markQ M).k = M.k := by
  unfold Fo.PlaneMat.markQ
  split <;> rfl

theorem famSum_le (p : K8.Par) {M0 n L B : ℕ}
    (h : ∀ q, q < n → p.ks.getD (M0 + q) 0 * (p.ms.getD (M0 + q) 0 / L) ≤ B) :
    OnBytes.Road.K4.Plan.famSum p (M0, n, L) ≤ n * B := by
  have h1 := List.sum_le_card_nsmul
    ((List.range n).map fun q => p.ks.getD (M0 + q) 0 * (p.ms.getD (M0 + q) 0 / L)) B (by
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact h q (List.mem_range.1 hq))
  simpa [famSum] using h1

/-- The two folds, side by side. -/
theorem units_aux : ∀ (l : List Attention.ACall) (a b : ℕ), a ≤ b →
    (l.filter fun c => c.kind == Attention.Table.kfd).foldl
        (fun a c => a + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length) a ≤
      l.foldl (fun n c => if c.kind == Attention.Table.kfd then n + c.segs.length else n) b
  | [], _, _, h => h
  | c :: l, a, b, h => by
    by_cases hc : (c.kind == Attention.Table.kfd) = true
    · rw [List.filter_cons_of_pos (p := fun c : Attention.ACall => c.kind == Attention.Table.kfd) (a := c) (l := l) hc,
        List.foldl_cons, List.foldl_cons, if_pos hc]
      exact units_aux l _ _ (Nat.add_le_add h (held_le c))
    · rw [List.filter_cons_of_neg (p := fun c : Attention.ACall => c.kind == Attention.Table.kfd) (a := c) (l := l) hc,
        List.foldl_cons, if_neg hc]
      exact units_aux l _ _ h

theorem att_units_le (S : Attention.Shape) :
    (S.calls.toList.filter fun c => c.kind == Attention.Table.kfd).foldl (fun a c => a + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length) 0 ≤
      S.calls.foldl (fun n c => if c.kind == Attention.Table.kfd then n + c.segs.length else n) 0 := by
  rw [← Array.foldl_toList]
  exact units_aux S.calls.toList 0 0 (Nat.le_refl 0)

theorem att_tabsEnd_le (S : Attention.Shape) (i : Attention.In) (p : K8.Par)
    (hk : p.ks = ((Attention.matrices S i).map Fo.PlaneMat.markQ).toList.map (·.k))
    (hm : p.ms = ((Attention.matrices S i).map Fo.PlaneMat.markQ).toList.map (·.m))
    (ha : p.asks = K8.Asks.attention S) : P5J.K8N.tabsEnd p ≤ S.tableElems := by
  have K : ∀ j, p.ks.getD j 0 = (((Attention.matrices S i).map Fo.PlaneMat.markQ).getD j {}).k := by
    intro j
    rw [hk]
    exact P5J.K8N.getD_k _ j
  have M : ∀ j, p.ms.getD j 0 = (((Attention.matrices S i).map Fo.PlaneMat.markQ).getD j {}).m := by
    intro j
    rw [hm]
    exact P5J.K8N.getD_m _ j
  have fAs : famSum p (0, S.cf.NAs, 2 ^ S.cf.lmS) ≤ S.cf.NAs * (S.kAs / S.cf.NAs) :=
    famSum_le p fun q hq => by
      rw [K, M, Nat.zero_add]
      exact att_tab_as _ markQ_m markQ_k S i hq
  have one : ∀ (j L B : ℕ),
      (((Attention.matrices S i).map Fo.PlaneMat.markQ).getD j {}).k *
        ((((Attention.matrices S i).map Fo.PlaneMat.markQ).getD j {}).m / L) ≤ B →
      famSum p (j, 1, L) ≤ B := by
    intro j L B h
    have := famSum_le p (M0 := j) (n := 1) (L := L) (B := B) fun q hq => by
      obtain rfl : q = 0 := by omega
      rw [K, M, Nat.add_zero]
      exact h
    rwa [Nat.one_mul] at this
  have fAh := one S.cf.NAs S.T _ (att_tab_ah _ markQ_m markQ_k S i)
  have fAo := one (S.cf.NAs + 1) (2 ^ S.cf.la) _ (att_tab_ao _ markQ_m markQ_k S i)
  have fBA := one (S.cf.NAs + 2) (2 ^ S.cf.lmb) _ (att_tab_bA _ markQ_m markQ_k S i)
  have fQa := one (S.cf.NAs + 3) (2 ^ S.cf.la) _ (att_tab_qa _ markQ_m markQ_k S i)
  have hn := att_units_le S
  have hAs : S.cf.NAs * (S.kAs / S.cf.NAs) ≤ S.kAs := Nat.mul_div_le _ _
  unfold P5J.K8N.tabsEnd
  rw [end_sum0, ha]
  unfold K8.Asks.attention Attention.Shape.tableElems
  dsimp only
  simp only [List.map_append, List.map_replicate, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, sum_rep, Nat.add_zero]
  generalize (S.calls.toList.filter fun c => c.kind == Attention.Table.kfd).foldl
    (fun a c => a + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length) 0 = n at hn ⊢
  generalize S.calls.foldl (fun n c => if c.kind == Attention.Table.kfd then n + c.segs.length else n) 0 = N at hn ⊢
  have t1 : 3 * famSum p (0, S.cf.NAs, 2 ^ S.cf.lmS) ≤ 3 * S.kAs :=
    Nat.mul_le_mul_left 3 (fAs.trans hAs)
  have t2 : (n + 6) * famSum p (S.cf.NAs, 1, S.T) ≤ (N + 6) * S.fillH :=
    Nat.mul_le_mul (Nat.add_le_add_right hn 6) fAh
  have t4 : (2 * n + 5) * famSum p (S.cf.NAs + 3, 1, 2 ^ S.cf.la) ≤
      (2 * N + 5) * (S.fillQ * S.T / 2 ^ S.cf.la) :=
    Nat.mul_le_mul (by omega) fQa
  have t5 : 3 * famSum p (S.cf.NAs + 2, 1, 2 ^ S.cf.lmb) ≤ 3 * S.kbA := Nat.mul_le_mul_left 3 fBA
  omega

end H2K5.Door

#print axioms H2K5.Door.markQ_m
#print axioms H2K5.Door.markQ_k
#print axioms H2K5.Door.famSum_le
#print axioms H2K5.Door.units_aux
#print axioms H2K5.Door.att_units_le
#print axioms H2K5.Door.att_tabsEnd_le
