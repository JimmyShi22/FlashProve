-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TieShape.lean: THE SMALLNESS TEST: THE VERIFIER's TEST ON A TIE's SHAPES
(`tieShapeHeld`, OnBytes/Model/Tail.lean: twenty clauses on the matrix's array of symbols, the
plan's numbers for the tie, the number of the tie's claim and the lengths of five vectors) SAYS YES
BEHIND THE ADDING. OF THE TWENTY CLAUSES: EIGHT ARE DRAWN FROM A YES OF THE RUN "K8.equations"
ALONE: five on the plan's numbers and the lengths of two vectors (the library's `Powered`,
OnBytes/Tie/Pv/Tail/EndClosed.lean; `rowX_size`, Johnson/Desc/K8/Honest/CoefClosed.lean) and that
the tie's claim has a number · FOUR FROM THAT YES AND A PREMISE: that number lies below the plan's
number of claims (with the premise on the number of claims, which `Added8.plan_bound` pays where
Added8 stands at the number of the claims in front) · the length of the row weights (`coef_mat`,
CoefClosed.lean; with the array's one row and "two matrices have two arrays") · the lengths of two
more vectors (the library's `eqWeights_spec`, Johnson/Desc/First/TailClaims/EquationsForms.lean;
with one public equation) · EIGHT ARE PREMISES CARRIED OVER: five on the array, three public
equations. WHAT THE RUN WRITES INTO `tieObj`, ON WHICH NO LAW OF THE LIBRARY WAS FOUND TO SPEAK, is
shown here. What a yes of the test means is the library's (`tieShapeHeld_iff`,
Johnson/Desc/First/TailClaims/AgainMeans.lean; `tieShapeHeld_eq`, AgainAgrees.lean). None of the
library's goals.

  `pushGet_lt`, `pushGet_size`   an array with one more entry, read
  `tieObj_fold`   a walk each of whose steps notes the number of the next claim and lays one claim:
                   what it has noted
  **`eqTail_tieObj`**   a yes of the run's tail ⊢ tl'.tieObj has NM entries, and entry mu is front +
                   ‹the claims laid before the tail› + mu
  `TieArrayAt tl Y mu`   at the ledger Y the array of matrix mu's symbols is of the kind "symbols",
                   has one virtual row, the plan's numbers of rows and of columns, and its row has a
                   weight for each of the plan's k columns
  `ShpPub tl mu`   three public equations on the plan's numbers for the tie: k is the matrix's k ·
                   K1 = k · Kc = k
  **`Added8.plan_bound`**   Added8 at the number of the claims in front ⊢ the claims in front and
                   the run's own are no more than the plan's number of claims: NO FURTHER PREMISE:
                   the adding tests it claim by claim (`addList_count`,
                   Johnson/Desc/K8/Honest/FallDraw.lean). The library has the like under two more
                   facts on the ledger (`K9L.addAll_bound`,
                   Johnson/Desc/First/Batch/Law/AddBound.lean): kin, not called
  **`Added8.tieShape`**   what a yes of the batching block opens (Added8) · mu < tl.NM · TieArrayAt
                   tl Y mu · ShpPub tl mu · two matrices have two arrays · the claims in front and
                   the run's own are no more than the plan's number of claims ⊢ tl'.tieShapeHeld
                   (coefBody tl' g G) mu = true
THE PROOF OF `eqTail_tieObj` WALKS THE RUN's TEXT AS THE PROOF OF `eqTail_total`
(Johnson/Desc/First/TailClaims/EquationsTotal.lean) DOES, line for line but for the sentence at each
tie.
Limits. AN IMPLICATION, AT ONE MATRIX mu: the "all" over the matrices in the verifier's test, and
the clauses that stand beside it there, are not here. `Added8`, `TieArrayAt`, `ShpPub` AND "two
matrices have two arrays" ARE PAID BY NOBODY HERE; the last premise, on the number of claims, is
paid by `Added8.plan_bound` where Added8 stands at the number of the claims in front. `TieArrayAt`
speaks of the ledger behind the runs. PAYERS IN SIGHT, NOT CALLED: "two matrices have two arrays"
and the first of ShpPub's three equations are clauses of the public test `symbolsLaid`
(Johnson/Desc/K8/Honest/SymbolsFew.lean). The run itself tests the first on the whole list of
arrays; that the list is as long as the number of matrices is a clause of the verifier's test on the
order (`orderB`, Johnson/Desc/K8/Honest/OrderShape.lean). THE SAME SENTENCE IS A PREMISE IN
Johnson/Desc/K8/Honest/SecondFew.lean AND CoefClosed.lean: whoever pays it pays all.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- An earlier entry of an array with one more entry. -/
theorem pushGet_lt (a : Array Nat) (v i : Nat) (hi : i < a.size) :
    (a.push v).getD i 0 = a.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  rw [if_neg (by omega)]

/-- The new entry. -/
theorem pushGet_size (a : Array Nat) (v : Nat) : (a.push v).getD a.size 0 = v := by
  simp [Array.getD_eq_getD_getElem?]

/-- A walk each of whose steps notes the number of the next claim and lays one claim. -/
theorem tieObj_fold (front : Nat) : ∀ (l : List Nat) (b : MProd (Array Nat) (Array Nat)) (s : St)
    (b' : MProd (Array Nat) (Array Nat)) (s' : St),
    RunFoldE (fun (_ : Nat) (b : MProd (Array Nat) (Array Nat)) (s : St)
      (b1 : MProd (Array Nat) (Array Nat)) (s1 : St) =>
      b1.fst = b.fst.push (front + s.2.size) ∧ s1.2.size = s.2.size + 1) l b s b' s' →
    b'.fst.size = b.fst.size + l.length ∧
      (∀ i, i < b.fst.size → b'.fst.getD i 0 = b.fst.getD i 0) ∧
      ∀ i, i < l.length → b'.fst.getD (b.fst.size + i) 0 = front + s.2.size + i
  | [], b, s, b', s', h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | _ :: l, b, s, b', s', h => by
    obtain ⟨b1, s1, ⟨e1, e2⟩, hr⟩ := h
    obtain ⟨c1, c3, c4⟩ := tieObj_fold front l b1 s1 b' s' hr
    have z1 : b1.fst.size = b.fst.size + 1 := by rw [e1, Array.size_push]
    refine ⟨by rw [c1, z1, List.length_cons]; omega, fun i hi => ?_, fun i hi => ?_⟩
    · rw [c3 i (by omega), e1]
      exact pushGet_lt _ _ _ hi
    · cases i with
      | zero =>
        rw [Nat.add_zero, c3 _ (by omega), e1]
        exact pushGet_size _ _
      | succ j =>
        have h4 := c4 j (by rw [List.length_cons] at hi; omega)
        rw [z1, e2] at h4
        rw [show b.fst.size + (j + 1) = b.fst.size + 1 + j by omega, h4]
        omega

/-- **WHAT A YES OF THE RUN's TAIL HAS WRITTEN INTO THE LIST OF THE TIES' CLAIMS' NUMBERS.** -/
theorem eqTail_tieObj (before : Nat) (tlb tl' : HTailF2) (funs : Array HFun)
    (front : Nat) (s s' : St) (h : eqTail before tlb funs front s = .ok (tl', s')) :
    ∃ tl1, eqWeights tlb front s = .ok (tl1, s) ∧ tl'.tieObj.size = tl1.NM ∧
      ∀ mu, mu < tl1.NM → tl'.tieObj.getD mu 0 = front + s.2.size + mu := by
  unfold eqTail at h
  obtain ⟨n0, t0, h0, k0⟩ := (eq_bind_ok _ _ _ _ _).1 h
  obtain ⟨en0, et0⟩ := eq_claims_ok h0
  rw [en0, et0] at k0
  obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 k0
  obtain ⟨-, et1⟩ := eq_must_ok h1
  rw [et1] at k1
  obtain ⟨tl1, t2, hW, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
  have eW : t2 = s := by
    unfold eqWeights at hW
    obtain ⟨x3, t3, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 hW
    rw [(eq_ask_ok g1).2] at g2
    exact (eq_get_ok g2).2
  rw [eW] at hW k2
  obtain ⟨sz, t3, h3, k3⟩ := (eq_bind_ok _ _ _ _ _).1 k2
  rw [(eq_ask_ok h3).2] at k3
  obtain ⟨bT, sT, hT, k4⟩ := (eq_bind_ok _ _ _ _ _).1 k3
  obtain ⟨bR, sR, hR, k5⟩ := (eq_bind_ok _ _ _ _ _).1 k4
  obtain ⟨u6, t6, h6, k6⟩ := (eq_bind_ok _ _ _ _ _).1 k5
  rw [(eq_must_ok h6).2] at k6
  obtain ⟨u7, t7, h7, k7⟩ := (eq_bind_ok _ _ _ _ _).1 k6
  rw [(eq_must_ok h7).2] at k7
  obtain ⟨g1, t8, h8, k8⟩ := (eq_bind_ok _ _ _ _ _).1 k7
  rw [(eq_get_ok h8).2] at k8
  obtain ⟨g3, t9, h9, k9⟩ := (eq_bind_ok _ _ _ _ _).1 k8
  rw [(eq_get_ok h9).2] at k9
  obtain ⟨kinds, t10, h10, k10⟩ := (eq_bind_ok _ _ _ _ _).1 k9
  rw [(eq_ask_ok h10).2] at k10
  obtain ⟨u11, t11, h11, k11⟩ := (eq_bind_ok _ _ _ _ _).1 k10
  rw [(eq_must_ok h11).2] at k11
  obtain ⟨u12, t12, h12, k12⟩ := (eq_bind_ok _ _ _ _ _).1 k11
  rw [(eq_must_ok h12).2] at k12
  obtain ⟨u13, t13, h13, k13⟩ := (eq_bind_ok _ _ _ _ _).1 k12
  rw [(eq_must_ok h13).2] at k13
  obtain ⟨etl, -⟩ := (eq_pure_ok _ _ _ _ _).1 k13
  have rT := forInE_inv front _
    (fun (_ : Nat) (b : MProd (Array Nat) (Array Nat)) (s : St)
      (b1 : MProd (Array Nat) (Array Nat)) (s1 : St) =>
      b1.fst = b.fst.push (front + s.2.size) ∧ s1.2.size = s.2.size + 1)
    (by
      intro mu b s r s1 hb
      obtain ⟨n, x1, c1, d1⟩ := (eq_bind_ok _ _ _ _ _).1 hb
      obtain ⟨en, ex1⟩ := eq_claims_ok c1
      rw [ex1] at d1
      obtain ⟨u, x2, c2, d2⟩ := (eq_bind_ok _ _ _ _ _).1 d1
      obtain ⟨u', x3, c3, d3⟩ := (eq_bind_ok _ _ _ _ _).1 d2
      rw [((eq_pure_ok _ _ _ _ _).1 c3).2] at d3
      obtain ⟨er, ex⟩ := (eq_pure_ok _ _ _ _ _).1 d3
      obtain ⟨cl, hcl, -⟩ := eqTie_step Reading.gl allZero tl1 mu s.1 front _ _ _ c2
      rw [ex, hcl]
      refine ⟨_, er, ?_, Array.size_push ..⟩
      show b.fst.push n = _
      rw [en]) _ _ _ _ _ hT
  obtain ⟨c1, -, c4⟩ := tieObj_fold front _ _ _ _ _ rT
  refine ⟨tl1, hW, ?_, fun mu hmu => ?_⟩
  · rw [etl]
    show bT.fst.size = _
    rw [c1, List.length_range]
    exact Nat.zero_add _
  · rw [etl]
    show bT.fst.getD mu 0 = _
    have h4 : bT.fst.getD (0 + mu) 0 = front + s.2.size + mu :=
      c4 mu (by rw [List.length_range]; exact hmu)
    rw [Nat.zero_add] at h4
    exact h4

/-- The array of a matrix's symbols at a ledger. -/
structure TieArrayAt (tl : HTailF2) (Y : Fork) (mu : Nat) : Prop where
  kind : (Y.trees.getD (tl.gtTree.getD mu 0) {}).kind = .symbols
  rows : (Y.trees.getD (tl.gtTree.getD mu 0) {}).rows.size = 1
  R : (Y.trees.getD (tl.gtTree.getD mu 0) {}).R = (tl.shp.getD mu {}).Rr
  K : (Y.trees.getD (tl.gtTree.getD mu 0) {}).K = (tl.shp.getD mu {}).Kc
  full : ((Y.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L.size = (tl.shp.getD mu {}).k

/-- Three public equations on the plan's numbers for a tie. -/
structure ShpPub (tl : HTailF2) (mu : Nat) : Prop where
  k : (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k
  K1 : (tl.shp.getD mu {}).K1 = (tl.shp.getD mu {}).k
  Kc : (tl.shp.getD mu {}).Kc = (tl.shp.getD mu {}).k

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- The claims in front and the run's own are no more than the plan's number of claims: the adding
itself tests it, claim by claim. -/
theorem Added8.plan_bound (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (hn : n₀ = fr.length) :
    n₀ + k8.length ≤ Y.planClaimsF := by
  have h := addList_count _ Y G A.sz A.add (by rw [A.n0]; exact Nat.zero_le _)
  rw [A.n0, List.length_append, List.length_append] at h
  omega

/-- **THE TEST ON A TIE's SHAPES SAYS YES BEHIND THE ADDING.** -/
theorem Added8.tieShape (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (mu : Nat) (hmu : mu < tl.NM) (T : TieArrayAt tl Y mu) (Sp : ShpPub tl mu)
    (hinj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b)
    (hpl : n₀ + k8.length ≤ Y.planClaimsF) :
    tl'.tieShapeHeld (coefBody tl' g G) mu = true := by
  obtain ⟨-, cp, hfr, -⟩ := A.core
  have eN : tl'.NM = tl.NM :=
    eq_same (·.NM) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eMa : tl'.mats = tl.mats :=
    eq_same (·.mats) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eShp : tl'.shp = tl.shp :=
    eq_same (·.shp) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eGt : tl'.gtTree = tl.gtTree :=
    eq_same (·.gtTree) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have hmu' : mu < tl'.NM := by rw [eN]; exact hmu
  obtain ⟨before, tla, tlb, s1, s2, arr, -, -, k9, harr⟩ := eq_parts A.eq
  obtain ⟨tl1, hW, hsz, hob⟩ := eqTail_tieObj before tlb tl' funs _ s2 _ k9
  obtain ⟨tl2, hW2, -, -, etl, -, new, hnew, hlen, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs _ s2 _ k9
  obtain rfl : tl1 = tl2 := congrArg Prod.fst (Except.ok.inj (hW.symm.trans hW2))
  obtain ⟨hP1, -, hgam1⟩ := eqWeights_spec tlb tl1 _ s2 s2 hW
  have eN1 : tl1.NM = tl'.NM := ((congrArg (·.NM) etl).trans rfl).symm
  have hP : Powered tl' s2.1.theta := by
    rw [etl]
    exact ⟨hP1.vp, hP1.vt, hP1.rowX, hP1.loX, hP1.eqFirst, hP1.shape⟩
  have hgam : tl'.gamX.getD mu #[] = gamAt tl' mu ∧ tl'.gamV.getD mu #[] = gamAt tl' mu := by
    have h0 := hgam1 mu (by rw [eN1]; exact hmu')
    rw [etl]
    exact h0
  have hlt := hP.lt_shp mu hmu'
  obtain ⟨sJ, sRd, sR, sRr, sm⟩ := hP.shape mu hmu'
  have zg : (gamAt tl' mu).size = (tl.shp.getD mu {}).k := by
    rw [gamAt, Array.size_map, Array.size_range, eMa, Sp.k]
  have zr := rowX_size hP hlt
  have zl : (tl'.loX.getD mu #[]).size = 1 := by
    rw [hP.loX]
    simp [Array.getD, hlt]
  rw [eShp] at sJ sRd sR sRr sm zr
  rw [eMa] at sm
  have lk : LinkJoin.look ((coefBody tl' g G).trees.getD (tl.gtTree.getD mu 0) {}) =
      LinkJoin.look (Y.trees.getD (tl.gtTree.getD mu 0) {}) :=
    (look_at (K9L.coef_looks tl' g G) _).trans (look_at (LinkJoin.looks_of_frame _ _ hfr) _)
  have rG : (G.trees.getD (tl'.gtTree.getD mu 0) {}).rows.size = 1 := by
    rw [eGt]
    exact (congrArg (·.2.2.2) (look_at (LinkJoin.looks_of_frame _ _ hfr) _)).trans T.rows
  have hc := coef_mat tl' g G hmu' (hasRow_of_rows rG (by omega)) (by
    rw [eN, eGt]
    exact hinj)
  rw [← coefBody_all, eGt] at hc
  have zc : (((coefBody tl' g G).trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).coef.size =
      (tl.shp.getD mu {}).mS := (congrArg Array.size hc).trans zr
  have zL : (((coefBody tl' g G).trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L.size =
      (tl.shp.getD mu {}).k := by
    have e1 : (((coefBody tl' g G).trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L =
        weightsOf G (tl.gtTree.getD mu 0) 0 := weights_coefBody tl' g G _ _
    rw [e1]
    show ((G.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L.size = _
    rw [lsize_of_frame, hfr, ← lsize_of_frame]
    exact T.full
  have bp : (coefBody tl' g G).planClaimsF = Y.planClaimsF :=
    (congrArg (·.2.2.2) (K9L.core_coefBody tl' g G)).trans cp
  have zk : k8.length = s2.2.size + new.length := by
    have e2 : arr = s2.2 ++ new.toArray := congrArg Prod.snd hnew
    have e3 : arr.size = s2.2.size + new.length := by
      rw [e2, Array.size_append]
      exact congrArg (s2.2.size + ·) List.size_toArray
    rw [← harr, Array.length_toList]
    exact e3
  have zo : tl'.tieObj.getD mu 0 < Y.planClaimsF := by
    rw [hob mu (by rw [eN1]; exact hmu')]
    have : mu < tl1.NM := by rw [eN1]; exact hmu'
    omega
  have h := (tieShapeHeld_iff tl' (coefBody tl' g G) mu).2 (by
    dsimp only
    rw [eShp, eGt, eMa, bp, hgam.1, hgam.2]
    exact ⟨(congrArg (·.1) lk).trans T.kind, (congrArg (·.2.2.2) lk).trans T.rows,
      (congrArg (·.2.1) lk).trans T.R, (congrArg (·.2.2.1) lk).trans T.K,
      by rw [hsz, eN1]; exact hmu', sm.symm, sJ, sR.trans sm, sRr.trans sm, sRd, Sp.k, Sp.K1,
      Sp.Kc, zr.trans sm, zl, zo, zc.trans sRr.symm, zL, zg, zg⟩)
  rw [tieShapeHeld_eq] at h
  exact h

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pushGet_lt
#print axioms VerifiableInference.Desc.First.K8.Honest.pushGet_size
#print axioms VerifiableInference.Desc.First.K8.Honest.tieObj_fold
#print axioms VerifiableInference.Desc.First.K8.Honest.eqTail_tieObj
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.plan_bound
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.tieShape
