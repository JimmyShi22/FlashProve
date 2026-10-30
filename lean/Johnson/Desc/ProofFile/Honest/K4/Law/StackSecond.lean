-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackSecond.lean: CONDITIONAL.

What is here. THE SECOND PASS's SUM IN THE BATCHED SUMCHECK's TWO LONG VECTORS (`passSum D 1`,
StackStart.lean) IS THE SECOND WEIGHT TIMES THE SECOND TOKEN SUMCHECK's SUMMAND AT ITS END POINT, ON
THE VALUES AS SENT (`Sides.summand`, Johnson/Desc/K4/Honest/Sides.lean): the second of the four
sentences from which StackStart.lean has the start form's worth. Panel by panel: the two sides that
`panelTabs` (Johnson/Desc/K4/Honest/Stack.lean) lays hold the factors of the products that `tripsOf`
makes, the first side besides the pass's weight. Statements and proofs.

  `tripSum`, `tripSum_flat`   the sum of a list of products
  `getD_amap_range`, `div_grid`, `mod_grid`   tools
  `tri_dot`, `elemOfB`, `elemOfB_open`, `plain_dot`, `panel_dot`   **one panel**
  `sum_of_mapM`, `mapM_at`   loops
  `second_pass`   **the second pass's sum**

Limits. At the reading `Reading.gl`. Premises: the maker of the job's data returns; the summand
returns; A FORM THAT HAS A VALUE ON THE READS AT THE TOKEN POINT ALONE HAS THE SAME VALUE ON THE
READS AT ALL POINTS SAMPLED SO FAR (hval): a hypothesis here, shown nowhere in this file.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackPass
import Johnson.Desc.ProofFile.Honest.K4.Law.TripsOf
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsTrips

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE maddE)
open OnBytes.Model (Reading Aff eqTab)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Road.K4.C (gl_foldl_maddE range_sum sum_grid)
open OnBytes.Desc.First.K4.Honest

/-- The sum of a list of products. -/
noncomputable def tripSum (l : List Trip) : Cb.Gl.E :=
  (l.map fun t => Reading.gl.val t.1 * (Reading.gl.val t.2.1 * Reading.gl.val t.2.2)).sum

theorem tripSum_append (l l' : List Trip) : tripSum (l ++ l') = tripSum l + tripSum l' := by
  unfold tripSum
  rw [List.map_append, List.sum_append]

/-- Lists laid end to end. -/
theorem tripSum_flat {β : Type} (out : β → List Trip) : ∀ L : List β,
    tripSum (L.flatMap out) = (L.map fun x => tripSum (out x)).sum
  | [] => rfl
  | x :: L => by
    rw [List.flatMap_cons, tripSum_append, tripSum_flat out L, List.map_cons, List.sum_cons]

theorem getD_amap_range {β : Type} (f : ℕ → β) (n j : ℕ) (hj : j < n) (d : β) :
    ((Array.range n).map f).getD j d = f j := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, if_pos hj]
  rfl

theorem div_grid (i ny yv : ℕ) (h : yv < ny) : (i * ny + yv) / ny = i := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]

theorem mod_grid (i ny yv : ℕ) (h : yv < ny) : (i * ny + yv) % ny = yv := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h]

variable {S : OnBytes.Desc.First.K4.Honest.Sides} {val val' : Aff → Option E} {om : Array E}
  {F : Array (Array E)} {hZ hR : Tab}

/-- **A panel whose rows carry the selector.** -/
theorem tri_dot (hval : ∀ a y, val' a = some y → val a = some y) (b : SBlk)
    (htri : b.tri = true) {x : Array E × Array E} {tr : Array Trip}
    (hx : panelTabs S val om F hZ hR b = some x)
    (ht : tripsOf S val' F (fun lm yv => hR.getD (S.routedAt lm yv) zeroE) b = some tr) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      Reading.gl.val (om.getD b.claim zeroE) * tripSum tr.toList := by
  unfold panelTabs at hx
  simp only [htri, ↓reduceIte] at hx
  obtain ⟨v0, hv0, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨cols, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain rfl := Option.some.inj hx
  unfold tripsOf at ht
  simp only [htri, ↓reduceIte] at ht
  obtain ⟨v0', hv0', ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain ⟨cols', hc', ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain rfl := Option.some.inj ht
  obtain rfl : v0 = v0' := Option.some.inj (hv0.symm.trans hv0')
  have hcol : ∀ yv, yv < b.ny → cols'.getD yv zeroE = cols.getD yv zeroE := by
    intro yv hyv
    have g := amapM_range_get _ hc hyv zeroE
    have g' := amapM_range_get _ hc' hyv zeroE
    cases hv : b.virt with
    | some k =>
      simp only [hv] at g g'
      exact (Option.some.inj g').symm.trans (Option.some.inj g)
    | none =>
      simp only [hv] at g g'
      exact Option.some.inj ((hval _ _ g').symm.trans g)
  rw [sum_grid _ b.ny b.ni]
  unfold tripSum
  rw [Array.toList_map, Array.toList_range, List.map_map, range_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  show _ = Reading.gl.val (om.getD b.claim zeroE) *
    (Reading.gl.val (mulE b.ec (b.wt.getD 0 zeroE)) * (Reading.gl.val (b.sl.getD i zeroE) *
      Reading.gl.val ((List.range b.ny).foldl (fun s yv => maddE s (cols'.getD yv zeroE)
        (at2 (F.getD v0 #[]) (S.kkOf v0) i yv)) zeroE)))
  rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun yv hyv => ?_
  have hyv' := Finset.mem_range.mp hyv
  have hj : i * b.ny + yv < b.ni * b.ny := by
    calc i * b.ny + yv < i * b.ny + b.ny := by omega
      _ = (i + 1) * b.ny := by rw [Nat.succ_mul]
      _ ≤ b.ni * b.ny := Nat.mul_le_mul_right _ hi'
  rw [getD_amap_range _ _ _ hj, getD_amap_range _ _ _ hj, div_grid i b.ny yv hyv',
    mod_grid i b.ny yv hyv', hcol yv hyv', Reading.gl.mul, Reading.gl.mul, Reading.gl.mul,
    Reading.gl.mul, Reading.gl.mul]
  ring

/-- The product at row i and column yv of a panel with two factors, as `tripsOf` makes it. -/
def elemOfB (S : OnBytes.Desc.First.K4.Honest.Sides) (val : Aff → Option E)
    (Fx : Array (Array E)) (b : SBlk) (A : ℕ → ℕ → Option Aff) (i yv : ℕ) : Option Trip := do
  let a ← val (← A i yv)
  let c ← match b.v0, b.B with
    | none, some B => do val (← B i yv)
    | some v0, _ => some (at2 (Fx.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
    | none, none => none
  pure ((mulE b.ec (b.wt.getD i zeroE), a, c) : Trip)

/-- That text, opened. -/
theorem elemOfB_open {val : Aff → Option E} {Fx : Array (Array E)} {b : SBlk}
    {A : ℕ → ℕ → Option Aff} {i yv : ℕ} {y : Trip} (h : elemOfB S val Fx b A i yv = some y) :
    ∃ f a c, A i yv = some f ∧ val f = some a ∧
      (match b.v0, b.B with
        | none, some B => (B i yv).bind val
        | some v0, _ => some (at2 (Fx.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv)
        | none, none => none) = some c ∧
      y = (mulE b.ec (b.wt.getD i zeroE), a, c) := by
  unfold elemOfB at h
  obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
  refine ⟨f, a, ?_⟩
  revert h
  cases b.v0 with
  | some v0 =>
    intro h
    exact ⟨_, hf, ha, rfl, (Option.some.inj h).symm⟩
  | none =>
    cases b.B with
    | none =>
      intro h
      cases h
    | some B =>
      intro h
      obtain ⟨g, hg, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      exact ⟨c, hf, ha, by
        show (B i yv).bind val = some c
        rw [hg]
        exact hc, (Option.some.inj h).symm⟩

/-- **A panel with two factors.** -/
theorem plain_dot (hval : ∀ a y, val' a = some y → val a = some y) (b : SBlk)
    (htri : b.tri = false) {x : Array E × Array E} {tr : Array Trip}
    (hx : panelTabs S val om F hZ hR b = some x)
    (ht : tripsOf S val' F (fun lm yv => hR.getD (S.routedAt lm yv) zeroE) b = some tr) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      Reading.gl.val (om.getD b.claim zeroE) * tripSum tr.toList := by
  -- the products
  unfold tripsOf at ht
  simp only [htri, Bool.false_eq_true, ↓reduceIte] at ht
  have hv : b.virt = none := by
    cases hv : b.virt with
    | none => rfl
    | some k =>
      rw [hv] at ht
      simp at ht
  rw [hv] at ht
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ht
  obtain ⟨A, hA, ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain ⟨rows, hr, ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain rfl := Option.some.inj ht
  have hr' : (Array.range b.ni).mapM
      (fun i => (Array.range b.ny).mapM (elemOfB S val' F b A i)) = some rows := hr
  have hrs : rows.size = b.ni := amapM_range_size _ hr'
  -- the two sides
  unfold panelTabs at hx
  simp only [htri, Bool.false_eq_true, ↓reduceIte, hv] at hx
  obtain ⟨A', hA', hx⟩ := Option.bind_eq_some_iff.mp hx
  obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
  obtain ⟨a, ha, hx⟩ := Option.bind_eq_some_iff.mp hx
  have hxc : ∃ c, (match b.v0, b.B with
      | none, some B =>
        (Array.range (b.ni * b.ny)).mapM fun j => (B (j / b.ny) (j % b.ny)).bind val
      | some v0, _ => some ((Array.range (b.ni * b.ny)).map fun j =>
          at2 (F.getD (v0 + j / b.ny) #[]) (S.kkOf (v0 + j / b.ny)) 0 (j % b.ny))
      | none, none => none) = some c ∧ x = (a, c) := by
    revert hx
    cases b.v0 with
    | some v0 =>
      intro hx
      exact ⟨_, rfl, (Option.some.inj hx).symm⟩
    | none =>
      cases b.B with
      | none =>
        intro hx
        cases hx
      | some B =>
        intro hx
        obtain ⟨c, hc, hx⟩ := Option.bind_eq_some_iff.mp hx
        exact ⟨c, hc, (Option.some.inj hx).symm⟩
  obtain ⟨c, hc, rfl⟩ := hxc
  -- both sums by row and column
  have tl : ∀ (u : Array Trip) k, u.toList.getD k trip0 = u.getD k trip0 := fun u k => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have tl2 : ∀ k, rows.toList.getD k #[] = rows.getD k #[] := fun k => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [sum_grid _ b.ny b.ni, Array.toList_flatMap, tripSum_flat, sum_by_number #[],
    Array.length_toList, hrs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have gi := amapM_range_get _ hr' hi' #[]
  have his : (rows.getD i #[]).size = b.ny := amapM_range_size _ gi
  rw [tl2]
  show _ = _ * tripSum (rows.getD i #[]).toList
  unfold tripSum
  rw [sum_by_number trip0, Array.length_toList, his, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yv hyv => ?_
  have hyv' := Finset.mem_range.mp hyv
  have hj : i * b.ny + yv < b.ni * b.ny := by
    calc i * b.ny + yv < i * b.ny + b.ny := by omega
      _ = (i + 1) * b.ny := by rw [Nat.succ_mul]
      _ ≤ b.ni * b.ny := Nat.mul_le_mul_right _ hi'
  rw [tl]
  obtain ⟨f, a', c', e1, e2, e3, e4⟩ := elemOfB_open (amapM_range_get _ gi hyv' trip0)
  rw [e4]
  -- the first side's entry
  have ga := amapM_range_get _ ha hj zeroE
  rw [div_grid i b.ny yv hyv', mod_grid i b.ny yv hyv'] at ga
  obtain ⟨f1, k1, ga⟩ := Option.bind_eq_some_iff.mp ga
  obtain ⟨a1, k2, ga⟩ := Option.bind_eq_some_iff.mp ga
  obtain rfl : f = f1 := Option.some.inj (e1.symm.trans k1)
  obtain rfl : a' = a1 := Option.some.inj ((hval _ _ e2).symm.trans k2)
  rw [← Option.some.inj ga]
  -- the second side's entry
  have gc : c.getD (i * b.ny + yv) zeroE = c' := by
    revert hc e3
    cases b.v0 with
    | some v0 =>
      intro hc e3
      rw [← Option.some.inj hc, getD_amap_range _ _ _ hj, div_grid i b.ny yv hyv',
        mod_grid i b.ny yv hyv']
      exact Option.some.inj e3
    | none =>
      cases b.B with
      | none =>
        intro hc _
        cases hc
      | some B =>
        intro hc e3
        have g2 := amapM_range_get _ hc hj zeroE
        rw [div_grid i b.ny yv hyv', mod_grid i b.ny yv hyv'] at g2
        obtain ⟨g, q1, q2⟩ := Option.bind_eq_some_iff.mp g2
        obtain ⟨g', q3, q4⟩ := Option.bind_eq_some_iff.mp e3
        obtain rfl : g = g' := Option.some.inj (q1.symm.trans q3)
        exact Option.some.inj (q2.symm.trans (hval _ _ q4))
  rw [gc]
  show Reading.gl.val (mulE (mulE (mulE (om.getD b.claim zeroE) b.ec) (b.wt.getD i zeroE)) a') *
    Reading.gl.val c' = Reading.gl.val (om.getD b.claim zeroE) *
      (Reading.gl.val (mulE b.ec (b.wt.getD i zeroE)) * (Reading.gl.val a' * Reading.gl.val c'))
  rw [Reading.gl.mul, Reading.gl.mul, Reading.gl.mul, Reading.gl.mul]
  ring

/-- **One panel.** -/
theorem panel_dot (hval : ∀ a y, val' a = some y → val a = some y) (b : SBlk)
    {x : Array E × Array E} {tr : Array Trip} (hx : panelTabs S val om F hZ hR b = some x)
    (ht : tripsOf S val' F (fun lm yv => hR.getD (S.routedAt lm yv) zeroE) b = some tr) :
    ∑ j ∈ Finset.range (b.ni * b.ny),
        Reading.gl.val (x.1.getD j zeroE) * Reading.gl.val (x.2.getD j zeroE) =
      Reading.gl.val (om.getD b.claim zeroE) * tripSum tr.toList := by
  cases htri : b.tri with
  | true => exact tri_dot hval b htri hx ht
  | false => exact plain_dot hval b htri hx ht

/-- A loop's answers laid end to end, against a sum over the loop's list. -/
theorem sum_of_mapM {α : Type} (g : α → Option (Array Trip)) (term : α → Cb.Gl.E) (k : Cb.Gl.E) :
    ∀ (l : List α) (L : List (Array Trip)), l.mapM g = some L →
    (∀ a ∈ l, ∀ tr, g a = some tr → term a = k * tripSum tr.toList) →
    (l.map term).sum = k * tripSum (L.flatMap Array.toList)
  | [], L, h, _ => by
    obtain rfl := Option.some.inj h
    simp [tripSum]
  | a :: l, L, h, hk => by
    obtain ⟨b, L', h1, h2, rfl⟩ := mapM_cons_some h
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, tripSum_append, mul_add,
      hk a (List.mem_cons_self ..) b h1,
      sum_of_mapM g term k l L' h2 fun a' ha' => hk a' (List.mem_cons_of_mem _ ha')]

/-- A loop that answers has an answer at each member. -/
theorem mapM_at {α β : Type} (f : α → Option β) : ∀ (l : List α) (L : List β),
    l.mapM f = some L → ∀ a ∈ l, ∃ b, f a = some b
  | [], _, _, a, ha => absurd ha (List.not_mem_nil)
  | x :: l, L, h, a, ha => by
    obtain ⟨b, L', h1, h2, _⟩ := mapM_cons_some h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨b, h1⟩
    · exact mapM_at f l L' h2 a ha'

/-- **THE SECOND PASS's SUM IS THE SECOND WEIGHT TIMES THE SECOND TOKEN SUMCHECK's SUMMAND AT ITS
END POINT ON THE VALUES AS SENT.** R: the reads at the token point alone. -/
theorem second_pass {p : Pts} {shownT : Array E} {D : StackData}
    (h : stackDataOn S p shownT = some D) {sT : E} (hs : S.summand shownT p.rt = some sT)
    (hval : ∀ R, S.readsTok p.rt = some R → ∀ a y,
      valAff? S.v R (fun _ => zeroE) a = some y → valAff? S.v D.R (fun _ => zeroE) a = some y) :
    passSum D 1 = Reading.gl.val (p.om.getD 1 zeroE) * Reading.gl.val sT := by
  obtain ⟨eS, eom, eF, eR, _, _, _, ⟨places, hp⟩, sides, hsd, _, _⟩ := stackDataOn_open h
  -- the summand, opened
  unfold Sides.summand at hs
  obtain ⟨R, hR, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain ⟨l, hl, hs⟩ := Option.bind_eq_some_iff.mp hs
  obtain rfl := Option.some.inj hs
  unfold Sides.trips at hl
  obtain ⟨x, hx, hl⟩ := Option.bind_eq_some_iff.mp hl
  rw [hp] at hx
  obtain rfl := Option.some.inj hx
  dsimp only at hl
  obtain ⟨L0, hL0, hl⟩ := Option.bind_eq_some_iff.mp hl
  obtain rfl := Option.some.inj hl
  rw [Array.mapM_eq_mapM_toList, Array.toList_filter] at hL0
  obtain ⟨L, hL, rfl⟩ := Option.map_eq_some_iff.mp hL0
  rw [Array.mapM_eq_mapM_toList] at hsd
  obtain ⟨Ls, hLs, _⟩ := Option.map_eq_some_iff.mp hsd
  rw [← Array.foldl_toList, foldl_trips, Reading.gl.zero, zero_add, Array.toList_flatMap]
  unfold passSum
  refine sum_of_mapM _ _ _ _ L hL fun b hb tr htr => ?_
  obtain ⟨hbl, hcl⟩ := List.mem_filter.mp hb
  obtain ⟨xs, hxs⟩ := mapM_at _ _ _ hLs b hbl
  rw [hxs]
  have hc1 : b.claim = 1 := by simpa using hcl
  rw [eS, eom, eF, eR] at hxs
  have := panel_dot (S := S) (val := fun a => valAff? S.v D.R (fun _ => zeroE) a)
    (val' := fun a => valAff? S.v R (fun _ => zeroE) a) (hval R hR) b hxs htr
  rw [hc1] at this
  exact this

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.elemOfB_open
#print axioms ProofFile.Honest.K4.plain_dot
#print axioms ProofFile.Honest.K4.panel_dot
#print axioms ProofFile.Honest.K4.sum_of_mapM
#print axioms ProofFile.Honest.K4.mapM_at
#print axioms ProofFile.Honest.K4.second_pass
#print axioms ProofFile.Honest.K4.tripSum_append
#print axioms ProofFile.Honest.K4.tripSum_flat
#print axioms ProofFile.Honest.K4.getD_amap_range
#print axioms ProofFile.Honest.K4.div_grid
#print axioms ProofFile.Honest.K4.mod_grid
#print axioms ProofFile.Honest.K4.tri_dot
