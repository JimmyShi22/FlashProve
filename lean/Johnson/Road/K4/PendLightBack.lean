-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PendLightBack.lean: THE OTHER DIRECTION OF Johnson/Road/K4/PendLight.lean: where
wsPending returns at the plan's leaving, the light test accepts: SO THE TWO TESTS ARE ONE BOOL.
Statements with their proofs: the routine's refusals, one by one.

  `add_inv` · `fold_inv` · `span_inv` · `cube_inv` · `pending_inv`: what a return of each routine
    says of sizes.
  `pend_back`: wsPending returns at planWoOf lay uis ⟹ pendB lay uis n S = true.
  **`rowLight_eq`**: rowLightB P g n lin = rowB P g n lin: AT EVERY PLAN, NO PREMISE.

WHY. A test at the proof file's entry that rejected where the sub-protocol could accept would turn
honest files away; and every law on rowB is a law on the light test by one rewriting.

Limits. Nothing is evaluated here. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.PendLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Pend

open OnBytes OnBytes.Model OnBytes.Flat
open OnBytes.Model.Layer (Pub)
open OnBytes.Params (LinShape)
open OnBytes.Desc.First.K4.Total (zeroFac zeroClaim planWoOf planWo rowB unitsOf)

theorem add_inv (lay : WsLay) {G G' : Array E} {c : WsRecClaim} {w : E}
    (h : wsGammaAdd G lay c w = .ok G') :
    G'.size = G.size ∧ ∃ u, lay.U[c.ui]? = some u ∧ gamLenOf u c = u.rows ∧
      c.f.length = u.g.length ∧ u.off + u.rows ≤ G.size := by
  unfold wsGammaAdd at h
  cases hU : lay.U[c.ui]? with
  | none =>
    rw [hU] at h
    exact nomatch h
  | some u =>
    rw [hU] at h
    simp only [] at h
    split at h
    · exact nomatch h
    · rename_i hc
      obtain rfl := Except.ok.inj h
      simp at hc
      obtain ⟨⟨a, b⟩, d⟩ := hc
      rw [size_wsGamma_eq] at a
      exact ⟨size_addInto _ _ _, u, rfl, a, b, d⟩

theorem fold_inv (lay : WsLay) : ∀ (l : List WsRecClaim) (G G' : Array E),
    l.foldlM (fun G c => wsGammaAdd G lay c oneE) G = .ok G' →
    G'.size = G.size ∧ ∀ c ∈ l, ∃ u, lay.U[c.ui]? = some u ∧ gamLenOf u c = u.rows ∧
      c.f.length = u.g.length ∧ u.off + u.rows ≤ G.size
  | [], G, G', h => by
    obtain rfl := Except.ok.inj h
    exact ⟨rfl, fun _ hc => nomatch hc⟩
  | c :: l, G, G', h => by
    rw [List.foldlM_cons] at h
    cases e : wsGammaAdd G lay c oneE with
    | error x =>
      rw [e] at h
      exact nomatch h
    | ok G1 =>
      rw [e] at h
      obtain ⟨s1, k1⟩ := add_inv lay e
      obtain ⟨s2, k2⟩ := fold_inv lay l G1 G' h
      refine ⟨s2.trans s1, fun c' hc' => ?_⟩
      rcases List.mem_cons.1 hc' with rfl | hm
      · exact k1
      · obtain ⟨u, a, b, d, t⟩ := k2 c' hm
        exact ⟨u, a, b, d, by rw [← s1]; exact t⟩

theorem rowPart_ui (lay : WsLay) (c : WsClaim) (ka : E) : (wsRowPart lay c ka).ui = c.ui := by
  unfold wsRowPart
  split <;> rfl

theorem span_inv (lay : WsLay) : ∀ (uis : List Nat) (r fl : Nat × Nat),
    (uis.map fun ui => wsRowPart lay (zeroClaim lay ui) zeroE).foldlM
      (fun (r : Nat × Nat) c =>
        match lay.U[c.ui]? with
        | none => throw "internal-gamma-rows"
        | some u => pure (min r.1 u.off, max r.2 (u.off + u.rows))) r =
      (.ok fl : Except String (Nat × Nat)) → spanFrom lay uis r = some fl
  | [], r, fl, h => by
    obtain rfl := Except.ok.inj h
    rfl
  | ui :: l, r, fl, h => by
    rw [List.map_cons, List.foldlM_cons] at h
    have e : (wsRowPart lay (zeroClaim lay ui) zeroE).ui = ui := rowPart_ui lay _ _
    unfold spanFrom
    cases hU : lay.U[ui]? with
    | none =>
      simp only [e, hU] at h
      exact nomatch h
    | some u =>
      simp only [e, hU] at h
      exact span_inv lay l _ fl h

theorem cube_inv {kRow firstRow : Nat} {v : Array E}
    (h : (stretchInTheCube kRow firstRow v).isSome = true) :
    kRow < 63 ∧ firstRow + v.size ≤ 2 ^ kRow ∧ coverB kRow firstRow v.size = true := by
  unfold stretchInTheCube at h
  split at h
  · rename_i hc
    simp only [] at h
    rw [lens_eq] at h
    split at h
    · rename_i hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact ⟨hc.1, hc.2, hs⟩
    · exact nomatch h
  · exact nomatch h

theorem pending_inv (lay : WsLay) (o : WsForkOut) (n : Nat) (S : LinShape)
    (h : (wsPending lay o n S).toOption.isSome = true) :
    ∃ first last, lay.m0 = S.matrixRows ∧ o.recs.isEmpty = false ∧ o.recs.length = n ∧
      wsSpan lay o.recs = .ok (first, last) ∧ first < last ∧ last ≤ lay.m0 ∧ S.kRow ≤ 62 ∧
      lay.m0 ≤ 2 ^ S.kRow ∧
      (∀ c ∈ o.recs, ∃ u, lay.U[c.ui]? = some u ∧ gamLenOf u c = u.rows ∧
        c.f.length = u.g.length ∧ u.off + u.rows ≤ last) ∧
      coverB S.kRow first (last - first) = true := by
  unfold wsPending at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · exact nomatch h
  · rename_i c1
    split at h
    · exact nomatch h
    · rename_i c2
      cases hs : wsSpan lay o.recs with
      | error x =>
        rw [hs] at h
        exact nomatch h
      | ok fl =>
        obtain ⟨first, last⟩ := fl
        rw [hs] at h
        simp only [] at h
        split at h
        · exact nomatch h
        · rename_i c3
          cases hG : List.foldlM (fun G c => wsGammaAdd G lay c oneE)
              (Array.replicate last zeroE) o.recs with
          | error x =>
            rw [hG] at h
            exact nomatch h
          | ok Gam =>
            rw [hG] at h
            simp only [] at h
            obtain ⟨sG, kG⟩ := fold_inv lay o.recs _ Gam hG
            rw [Array.size_replicate] at sG
            simp at c1 c2 c3
            have sx : (Gam.extract first last).size = last - first := by
              rw [Array.size_extract, sG]
              omega
            cases hw : memberWeightsOnRows S first (Gam.extract first last) with
            | none =>
              rw [hw] at h
              exact nomatch h
            | some g =>
              unfold memberWeightsOnRows at hw
              split at hw
              · have k := cube_inv (by rw [hw]; rfl)
                rw [sx] at k
                refine ⟨first, last, c1, by simpa using c2.1.1, c2.1.2, rfl, by omega,
                  by omega, by omega, by omega, fun c hc => ?_, k.2.2⟩
                obtain ⟨u, a, b, d, t⟩ := kG c hc
                exact ⟨u, a, b, d, by rw [Array.size_replicate] at t; exact t⟩
              · exact nomatch hw

theorem pend_back {lay : WsLay} {uis : List Nat} {n : Nat} {S : LinShape}
    (h : (wsPending lay (planWoOf lay uis) n S).toOption.isSome = true) :
    pendB lay uis n S = true := by
  obtain ⟨first, last, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := pending_inv lay _ n S h
  have hs : spanFrom lay uis (2 ^ 64 - 1, 0) = some (first, last) := span_inv lay uis _ _ a4
  unfold pendB
  rw [hs]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨a1, ?_⟩, ?_⟩, a5⟩, a6⟩, a7⟩, a8⟩, ?_⟩, a10⟩
  · cases uis <;> simp_all [planWoOf]
  · simpa [planWoOf] using a3
  · intro ui hui
    obtain ⟨u, b1, b2, _, b4⟩ := a9 _ (List.mem_map.2 ⟨ui, hui, rfl⟩)
    rw [rowPart_ui] at b1
    have b1' : lay.U[ui]? = some u := b1
    unfold unitOkB
    rw [b1']
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    exact ⟨(gamLenOf_zero b1').symm.trans b2, b4⟩

/-- **The two tests are one Bool.** -/
theorem rowLight_eq (P : Pub) (g n : Nat) (lin : LinShape) :
    rowLightB P g n lin = rowB P g n lin := by
  cases hb : rowB P g n lin with
  | true =>
    unfold rowB planWo at hb
    unfold rowLightB
    cases hu : unitsOf P g with
    | none =>
      rw [hu] at hb
      exact nomatch hb
    | some uis =>
      rw [hu] at hb
      exact pend_back hb
  | false =>
    cases hl : rowLightB P g n lin with
    | false => rfl
    | true =>
      rw [row_light hl] at hb
      exact nomatch hb

end OnBytes.Road.K4.Pend

#print axioms OnBytes.Road.K4.Pend.pending_inv
#print axioms OnBytes.Road.K4.Pend.pend_back
#print axioms OnBytes.Road.K4.Pend.rowLight_eq
