-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PendLight.lean: THE TEST "wsPending returns at the plan's leaving" (`rowB`,
Johnson/Road/K4/Total/PlanRowDefs.lean) FOLLOWS FROM A TEST THAT WALKS NO ARRAY: arithmetic on the
layout's units alone. The definitions: Johnson/Road/K4/PendLightDefs.lean. Statements with their
proofs: sizes, by the library's own lemmas (OnBytes/Flat/PendingSizes.lean).

  `facLen` · `gamLenOf`: the length of a row factor's table and of a claim's coefficients, from
    sizes. `tabLen` · `gamLen`: the same at the claim at zeros, from the group's and the unit's
    numbers.
  `blockLens` · `coverB`: the lengths of the aligned blocks into which a stretch of rows is cut;
    they sum to the stretch's length.
  `spanFrom` · `unitOkB` · **`pendB lay uis n S`**: THE LIGHT TEST: every unit is in the layout ·
    the layout's rows are the shape's · the units are n, and not none · first < last ≤ m0 ≤ 2 ^
    kRow, kRow ≤ 62 · at each unit the coefficients are as many as its rows and its rows end at last
    or before · the blocks cover the stretch.
  `pending_returns`: wsPending returns at any leaving under these facts. **`pend_light`**: unitsOf P
  g = some uis · pendB P.wsLay uis n lin = true ⟹ rowB P g n lin = true. `rowLightB` · `row_light`:
  the same as one test on the plan. `pendB_nil`: at no unit the light test rejects.

WHY. wsPending lays a vector over the committed table's rows up to the stretch's end (some three
million at the full size), adds each claim's written-out coefficients and cuts the stretch into
blocks; whether it returns hangs on sizes.

Limits. ONE DIRECTION HERE; the other stands in Johnson/Road/K4/PendLightBack.lean: by `rowLight_eq`
the light test and rowB are one Bool at every plan. Nothing is evaluated here. K04_law, the law of
K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import OnBytes.Flat.PendingSizes
import Johnson.Road.K4.PendLightDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Pend

open OnBytes OnBytes.Model OnBytes.Flat
open OnBytes.Model.Layer (Pub)
open OnBytes.Params (LinShape)
open OnBytes.Desc.First.K4.Total (zeroFac zeroClaim planWoOf planWo rowB unitsOf)

/-! ## A claim's coefficients: how many -/

/-- The length of a row factor's table. -/
def facLen (x : WsRowFac) (G : WsGrp) : Nat :=
  if G.cls == 'E' then x.HV.size * 2 ^ x.pl.size else if G.aTaken then 1 else x.AV.size

theorem size_table_eq (x : WsRowFac) (G : WsGrp) : (x.table G).size = facLen x G := by
  unfold WsRowFac.table facLen
  split
  · rw [size_wsOuter, size_eqTab]
  · split <;> rfl

theorem size_fold_eq (l : List (WsRowFac × WsGrp)) : ∀ v : Array E,
    (l.foldl (fun v y => wsOuter v (y.1.table y.2)) v).size =
      l.foldl (fun n y => n * facLen y.1 y.2) v.size := by
  induction l with
  | nil => intro v; rfl
  | cons y l ih =>
    intro v
    rw [List.foldl_cons, List.foldl_cons, ih, size_wsOuter, size_table_eq]

/-- The number of a claim's coefficients on the rows of its unit. -/
def gamLenOf (u : WsUnit) (c : WsRecClaim) : Nat :=
  (c.f.zip u.g).reverse.foldl (fun n y => n * facLen y.1 y.2) u.nlw

theorem size_wsGamma_eq (u : WsUnit) (c : WsRecClaim) (w : E) :
    (wsGamma u c w).size = gamLenOf u c := by
  unfold wsGamma gamLenOf
  rw [size_fold_eq]
  have e : (wsDigits u.nlw (mulE w c.ka)).toArray.size = u.nlw := by simp [length_wsDigits]
  rw [e]

/-! ## Adding them up returns -/

theorem add_returns (lay : WsLay) {G : Array E} {c : WsRecClaim} {u : WsUnit}
    (hU : lay.U[c.ui]? = some u) (h1 : gamLenOf u c = u.rows) (h2 : c.f.length = u.g.length)
    (h3 : u.off + u.rows ≤ G.size) (w : E) :
    ∃ G', wsGammaAdd G lay c w = .ok G' ∧ G'.size = G.size := by
  unfold wsGammaAdd
  rw [hU]
  simp only []
  have hc : ((wsGamma u c w).size != u.rows || c.f.length != u.g.length ||
      decide (G.size < u.off + u.rows)) = false := by
    rw [size_wsGamma_eq, h1, h2]
    simpa using h3
  rw [hc]
  split
  · rename_i hx
    exact nomatch hx
  · exact ⟨_, rfl, size_addInto _ _ _⟩

theorem fold_returns (lay : WsLay) : ∀ (l : List WsRecClaim) (G : Array E),
    (∀ c ∈ l, ∃ u, lay.U[c.ui]? = some u ∧ gamLenOf u c = u.rows ∧ c.f.length = u.g.length ∧
      u.off + u.rows ≤ G.size) →
    ∃ G', l.foldlM (fun G c => wsGammaAdd G lay c oneE) G = .ok G' ∧ G'.size = G.size
  | [], G, _ => ⟨G, rfl, rfl⟩
  | c :: l, G, h => by
    obtain ⟨u, hU, h1, h2, h3⟩ := h c (by simp)
    obtain ⟨G1, e1, s1⟩ := add_returns lay hU h1 h2 h3 oneE
    obtain ⟨G2, e2, s2⟩ := fold_returns lay l G1 fun c' hc' => by
      obtain ⟨u', a, b, d, e⟩ := h c' (by simp [hc'])
      exact ⟨u', a, b, d, by rw [s1]; exact e⟩
    refine ⟨G2, ?_, s2.trans s1⟩
    rw [List.foldlM_cons, e1]
    exact e2

/-! ## The blocks cover the stretch -/

theorem block_len (kRow start firstRow d : Nat) (v : Array E) :
    (if d == 0 then
        ({ scalar := v.getD (start - firstRow) zeroE } : Tensor).insertChoice 0 kRow start
      else
        ((({} : Tensor).pushDense d).insertChoice d (kRow - d) (start / 2 ^ d)).setValues v
          (start - firstRow)).denseVars.length = d := by
  split
  · rename_i h
    have e : d = 0 := by simpa using h
    subst e
    rfl
  · simp [Tensor.setValues, Tensor.insertChoice, Tensor.pushDense]

theorem lens_eq (kRow firstRow : Nat) (v : Array E) : ∀ fuel start,
    (stretchBlocks kRow firstRow v fuel start).map (fun t => 2 ^ t.denseVars.length) =
      blockLens kRow firstRow v.size fuel start
  | 0, _ => rfl
  | fuel + 1, start => by
    unfold stretchBlocks blockLens
    simp only []
    split
    · rfl
    · simp only [List.map_cons, block_len, lens_eq kRow firstRow v fuel]

theorem cube_returns {kRow firstRow : Nat} {v : Array E} (h1 : kRow < 63)
    (h2 : firstRow + v.size ≤ 2 ^ kRow) (h3 : coverB kRow firstRow v.size = true) :
    (stretchInTheCube kRow firstRow v).isSome = true := by
  unfold stretchInTheCube
  have c : (decide (kRow < 63) && decide (firstRow + v.size ≤ 2 ^ kRow)) = true := by
    simp [h1, h2]
  rw [if_pos c]
  simp only []
  rw [lens_eq]
  unfold coverB at h3
  rw [if_pos h3]
  rfl

/-! ## The routine wsPending returns -/

theorem pending_returns (lay : WsLay) (o : WsForkOut) (n : Nat) (S : LinShape) {first last : Nat}
    (h1 : lay.m0 = S.matrixRows) (h2 : o.recs.isEmpty = false) (h3 : o.recs.length = n)
    (h4 : o.rm.size = lay.lk) (h5 : wsSpan lay o.recs = .ok (first, last)) (h6 : first < last)
    (h7 : last ≤ lay.m0) (h8 : S.kRow ≤ 62) (h9 : lay.m0 ≤ 2 ^ S.kRow)
    (h10 : ∀ c ∈ o.recs, ∃ u, lay.U[c.ui]? = some u ∧ gamLenOf u c = u.rows ∧
      c.f.length = u.g.length ∧ u.off + u.rows ≤ last)
    (h11 : coverB S.kRow first (last - first) = true) :
    (wsPending lay o n S).toOption.isSome = true := by
  obtain ⟨Gam, eG, sG⟩ := fold_returns lay o.recs (Array.replicate last zeroE) fun c hc => by
    obtain ⟨u, a, b, d, e⟩ := h10 c hc
    exact ⟨u, a, b, d, by rw [Array.size_replicate]; exact e⟩
  have sx : (Gam.extract first last).size = last - first := by
    rw [Array.size_extract, sG, Array.size_replicate]
    omega
  have hw : (memberWeightsOnRows S first (Gam.extract first last)).isSome = true := by
    unfold memberWeightsOnRows
    rw [if_pos (by rw [sx]; omega)]
    exact cube_returns (by omega) (by rw [sx]; omega) (by rw [sx]; exact h11)
  obtain ⟨g, eg⟩ := Option.isSome_iff_exists.1 hw
  unfold wsPending
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  split
  · rename_i hx
    simp [h1] at hx
  · split
    · rename_i hx
      simp [h2, h3, h4] at hx
    · rw [h5]
      simp only []
      split
      · rename_i hx
        simp at hx
        omega
      · rw [eG]
        simp only []
        rw [eg]
        rfl

/-! ## At the plan's leaving -/

theorem facLen_zero (G : WsGrp) : facLen ((zeroFac G).onRows G) G = tabLen G := by
  unfold facLen tabLen
  by_cases h : (G.cls == 'E') = true
  · rw [if_pos h, if_pos h]
    have e : ((zeroFac G).onRows G).HV.size = G.o := by simp [WsFac.onRows, zeroFac, h]
    rw [e]
  · rw [if_neg h, if_neg h]
    by_cases h2 : G.aTaken = true
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      simp [WsFac.onRows, zeroFac, h, h2]

theorem rowPart_at {lay : WsLay} {ui : Nat} {u : WsUnit} (h : lay.U[ui]? = some u) :
    wsRowPart lay (zeroClaim lay ui) zeroE =
      { ui := ui, ka := zeroE, f := ((u.g.map zeroFac).zip u.g).map fun y => y.1.onRows y.2 } := by
  unfold wsRowPart zeroClaim
  simp [h]

theorem zip_zero (l : List WsGrp) :
    (((l.map zeroFac).zip l).map fun y => y.1.onRows y.2).zip l =
      l.map fun G => ((zeroFac G).onRows G, G) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, ih]

theorem gamLenOf_zero {lay : WsLay} {ui : Nat} {u : WsUnit} (h : lay.U[ui]? = some u) :
    gamLenOf u (wsRowPart lay (zeroClaim lay ui) zeroE) = gamLen u := by
  rw [rowPart_at h]
  unfold gamLenOf gamLen
  simp only []
  rw [zip_zero, ← List.map_reverse, List.foldl_map]
  simp only [facLen_zero]

theorem span_plan (lay : WsLay) : ∀ (uis : List Nat) (r fl : Nat × Nat), spanFrom lay uis r = some
fl →
    (uis.map fun ui => wsRowPart lay (zeroClaim lay ui) zeroE).foldlM
      (fun (r : Nat × Nat) c =>
        match lay.U[c.ui]? with
        | none => throw "internal-gamma-rows"
        | some u => pure (min r.1 u.off, max r.2 (u.off + u.rows))) r =
      (.ok fl : Except String (Nat × Nat))
  | [], r, fl, h => by
    obtain rfl : r = fl := Option.some.inj h
    rfl
  | ui :: l, r, fl, h => by
    unfold spanFrom at h
    cases hU : lay.U[ui]? with
    | none =>
      rw [hU] at h
      exact nomatch h
    | some u =>
      rw [hU] at h
      rw [List.map_cons, List.foldlM_cons, rowPart_at hU]
      simp only [hU]
      exact span_plan lay l _ fl h

theorem pend_returns {lay : WsLay} {uis : List Nat} {n : Nat} {S : LinShape}
    (h : pendB lay uis n S = true) :
    (wsPending lay (planWoOf lay uis) n S).toOption.isSome = true := by
  unfold pendB at h
  cases hs : spanFrom lay uis (2 ^ 64 - 1, 0) with
  | none =>
    rw [hs] at h
    exact nomatch h
  | some fl =>
    rw [hs] at h
    obtain ⟨first, last⟩ := fl
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
      List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩ := h
    refine pending_returns lay (planWoOf lay uis) n S a1 ?_ ?_ ?_ (span_plan lay uis _ _ hs) a4 a5
      a6 a7 ?_ a9
    · cases uis <;> simp_all [planWoOf]
    · simp [planWoOf, a3]
    · simp [planWoOf]
    · intro c hc
      obtain ⟨ui, hui, rfl⟩ := List.mem_map.1 hc
      have t := a8 ui hui
      unfold unitOkB at t
      cases hU : lay.U[ui]? with
      | none =>
        rw [hU] at t
        exact nomatch t
      | some u =>
        rw [hU] at t
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at t
        refine ⟨u, by rw [rowPart_at hU]; exact hU, (gamLenOf_zero hU).trans t.1, ?_, t.2⟩
        rw [rowPart_at hU]
        simp

/-- **The light test gives the test on the routine wsPending.** -/
theorem pend_light {P : Pub} {g n : Nat} {lin : LinShape} {uis : List Nat}
    (hu : unitsOf P g = some uis) (h : pendB P.wsLay uis n lin = true) :
    rowB P g n lin = true := by
  unfold rowB planWo
  rw [hu]
  exact pend_returns h

theorem row_light {P : Pub} {g n : Nat} {lin : LinShape} (h : rowLightB P g n lin = true) :
    rowB P g n lin = true := by
  unfold rowLightB at h
  cases hu : unitsOf P g with
  | none =>
    rw [hu] at h
    exact nomatch h
  | some uis =>
    rw [hu] at h
    exact pend_light hu h

/-- At no unit the light test rejects. -/
theorem pendB_nil (lay : WsLay) (n : Nat) (S : LinShape) : pendB lay [] n S = false := by
  unfold pendB spanFrom
  simp

end OnBytes.Road.K4.Pend

#print axioms OnBytes.Road.K4.Pend.pending_returns
#print axioms OnBytes.Road.K4.Pend.pend_light
#print axioms OnBytes.Road.K4.Pend.row_light
#print axioms OnBytes.Road.K4.Pend.pendB_nil
