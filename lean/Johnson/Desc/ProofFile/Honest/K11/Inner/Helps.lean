-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/Helps.lean: small lemmas for the proof of `HeadMergeInner`
(Honest/K11/Inner/Statement.lean), with their proofs.

  `shapeOk_headMerge`   the call's shape passes the part's tests on the plan
  `claimVal_inside`, `rowAt_inside`   what a claim speaks of, and a row read at a point, see the
                        matrix inside its rows and columns alone
  `forall2_getD`        two lists of one length, member by member
  `gamma_rows_at`       a claim has as many weights on the rows as its unit has rows, at any scalar
  `gammaFold_returns`   the fold that writes the weights for the rows out returns
  `drawnE_last`         the last challenge's element

Limits. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Inner.Statement
import Johnson.Desc.K11.Honest.Law.Ends

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E mulE zeroE oneE)
open OnBytes.Model (Reading Aff World WsLay WsUnit WsClaim WsRecClaim wsClaimShape wsRowPart
  wsGamma wsGammaAdd wsEpsT)
open OnBytes.Road (Wm Numerals UnitOK GrpOK claimVal rowAt)
open VerifiableInference.Desc.Part.MaskedSum (Var shapeOk)

theorem shapeOk_headMerge (lk : Nat) : shapeOk (headMergeShape lk) = true := by
  have a : ((List.replicate lk (Var.plain 3)).all fun v =>
      decide (2 ≤ v.d) && decide (v.d ≤ 65)) = true :=
    List.all_eq_true.mpr fun v hv => by
      rw [(List.mem_replicate.1 hv).2]
      rfl
  show (((List.replicate lk (Var.plain 3)).all fun v => decide (2 ≤ v.d) && decide (v.d ≤ 65)) &&
    (decide (1 ≤ 1) && decide (1 ≤ 1))) = true
  rw [a]
  rfl

section Read
variable {K : Type} [Field K] {ρ : Reading K}

/-- What a claim speaks of sees the matrix inside its rows and columns alone. -/
theorem claimVal_inside (hρ : Numerals ρ) {lay : WsLay} {q : WsClaim} {u : WsUnit}
    (hu : lay.U[q.ui]? = some u) (hs : wsClaimShape lay q = .ok ()) (U : UnitOK lay.lk u)
    (hin : u.off + u.rows ≤ lay.m0) (W W' : Wm K)
    (hW : ∀ r k, r < lay.m0 → k < 2 ^ lay.lk → W r k = W' r k) :
    claimVal ρ lay W q = claimVal ρ lay W' q := by
  have a := OnBytes.Road.claim_cells hρ hu hs U W oneE oneE
  have b := OnBytes.Road.claim_cells hρ hu hs U W' oneE oneE
  rw [ρ.one, one_mul, one_mul] at a b
  rw [← a, ← b]
  refine Finset.sum_congr rfl fun C hC => Finset.sum_congr rfl fun y hy => ?_
  have hy' := Finset.mem_range.1 hy
  rw [hW _ _ (by omega) (Finset.mem_range.1 hC)]

/-- So does a row read at a point. -/
theorem rowAt_inside (ρ : Reading K) (lk m0 : Nat) (rm : Array E) (W W' : Wm K)
    (hW : ∀ r k, r < m0 → k < 2 ^ lk → W r k = W' r k) (y : Nat) (hy : y < m0) :
    rowAt ρ lk rm W y = rowAt ρ lk rm W' y := by
  unfold rowAt
  refine Finset.sum_congr rfl fun C hC => ?_
  rw [hW y C hy (Finset.mem_range.1 hC)]

end Read

theorem arr_getD_toList {α : Type} (a : Array α) (j : Nat) (d : α) :
    a.toList.getD j d = a.getD j d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- Two lists of one length, member by member. -/
theorem forall2_getD {α β : Type} (R : α → β → Prop) (da : α) (db : β) :
    ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
      (∀ a, a < l2.length → R (l1.getD a da) (l2.getD a db)) → List.Forall₂ R l1 l2
  | [], [], _, _ => .nil
  | x :: l1, y :: l2, hl, h =>
    .cons (h 0 (by simp)) (forall2_getD R da db l1 l2 (by simpa using hl) fun a ha => by
      have e := h (a + 1) (by simpa using ha)
      simpa using e)
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- What is left of a claim, its unit laid in. -/
theorem rowPart_fields {lay : WsLay} {q : WsClaim} {u : WsUnit} (hu : lay.U[q.ui]? = some u)
    (ka : E) :
    wsRowPart lay q ka =
      { ui := q.ui, ka := ka, f := (q.f.zip u.g).map fun y => y.1.onRows y.2 } := by
  unfold wsRowPart
  rw [hu]

/-- A claim has as many weights on the rows as its unit has rows, at any scalar. -/
theorem gamma_rows_at {lay : WsLay} {q : WsClaim} {u : WsUnit} (hu : lay.U[q.ui]? = some u)
    (hs : wsClaimShape lay q = .ok ()) (U : UnitOK lay.lk u) (ka : E) :
    (wsGamma u (wsRowPart lay q ka) oneE).size = u.rows := by
  obtain ⟨hlen, hfits⟩ := OnBytes.Road.shape_of_claim hu hs
  have hmap : (q.f.zip u.g).map (·.2) = u.g := List.map_snd_zip (by omega)
  have hok : ∀ y ∈ q.f.zip u.g, GrpOK y.2 ∧ y.1.fits y.2 = true := fun y hy =>
    ⟨U.grp y.2 (by
      have h1 : y.2 ∈ (q.f.zip u.g).map (·.2) := List.mem_map_of_mem hy
      rw [hmap] at h1
      exact h1), hfits y hy⟩
  have hleft : (q.f.zip u.g).map (·.2.left) = u.g.map (·.left) := by
    conv_rhs => rw [← hmap]
    rw [List.map_map]
    rfl
  rw [OnBytes.Road.wsGamma_eq hu, OnBytes.Road.gamOf_size _ hok, hleft, U.rows, List.size_toArray,
    OnBytes.Road.wsDigits_length]

/-- One step of the fold returns, and keeps the array's size. -/
theorem gammaAdd_returns {lay : WsLay} {q : WsClaim} {u : WsUnit} (hu : lay.U[q.ui]? = some u)
    (hs : wsClaimShape lay q = .ok ()) (U : UnitOK lay.lk u) (ka : E) (A : Array E)
    (hA : u.off + u.rows ≤ A.size) :
    ∃ A', wsGammaAdd A lay (wsRowPart lay q ka) oneE = .ok A' ∧ A'.size = A.size := by
  have hui : (wsRowPart lay q ka).ui = q.ui := by rw [rowPart_fields hu]
  have hfl : (wsRowPart lay q ka).f.length = u.g.length := by
    rw [rowPart_fields hu]
    show ((q.f.zip u.g).map _).length = _
    rw [List.length_map, List.length_zip, (OnBytes.Road.shape_of_claim hu hs).1, Nat.min_self]
  have hc : ((wsGamma u (wsRowPart lay q ka) oneE).size != u.rows ||
      (wsRowPart lay q ka).f.length != u.g.length || decide (A.size < u.off + u.rows)) = false := by
    rw [gamma_rows_at hu hs U ka, hfl]
    simp
    omega
  have hr : ∃ A', wsGammaAdd A lay (wsRowPart lay q ka) oneE = .ok A' := by
    unfold wsGammaAdd
    rw [hui, hu]
    simp only [hc]
    exact ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ := hr
  exact ⟨A', hA', (OnBytes.Road.gammaAdd_sum (K := Cb.Gl.E) Reading.gl (by rw [hui]; exact hu) hA'
    fun _ => 0).1⟩

/-- **The fold that writes the weights for the rows out returns.** -/
theorem gammaFold_returns (lay : WsLay) : ∀ (cr : List (WsClaim × E)) (f : WsClaim × E → E)
    (A : Array E),
    (∀ y ∈ cr, ∃ u, lay.U[y.1.ui]? = some u ∧ wsClaimShape lay y.1 = .ok () ∧ UnitOK lay.lk u ∧
      u.off + u.rows ≤ A.size) →
    ∃ Gam, (cr.map fun y => wsRowPart lay y.1 (f y)).foldlM
      (fun A r => wsGammaAdd A lay r oneE) A = .ok Gam
  | [], _, A, _ => ⟨A, rfl⟩
  | y :: cr, f, A, h => by
    obtain ⟨u, hu, hs, U, hA⟩ := h y List.mem_cons_self
    obtain ⟨A', hA', hsz⟩ := gammaAdd_returns hu hs U (f y) A hA
    obtain ⟨Gam, hG⟩ := gammaFold_returns lay cr f A' fun z hz => by
      obtain ⟨u', a1, a2, a3, a4⟩ := h z (List.mem_cons_of_mem _ hz)
      exact ⟨u', a1, a2, a3, by rw [hsz]; exact a4⟩
    refine ⟨Gam, ?_⟩
    rw [List.map_cons, List.foldlM_cons, hA']
    exact hG

/-- The last challenge's element. -/
theorem drawnE_last (l : List Fmt.Drawn) (d : Fmt.Drawn) (x : Fmt.Ext) (h : l.getLast? = some d)
    (hd : d.elems = [x]) : (drawnE l).getLastD zeroE = E.ofTriple x := by
  unfold drawnE
  rw [List.getLastD_eq_getLast?, List.getLast?_map, h]
  show (Option.map E.ofTriple d.elems.head?).getD zeroE = _
  rw [hd]
  rfl

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.claimVal_inside
#print axioms ProofFile.Honest.K11.gammaFold_returns
