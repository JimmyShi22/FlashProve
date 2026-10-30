-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TiesClause.lean: THE SMALLNESS TEST: SIX OF THE EIGHT CONJUNCTS OF ONE CLAUSE
OF THE VERIFIER's TEST ON WHAT THE ADDING HAS LEFT (OnBytes/Model/Tail.lean, "tileSelfTestF"; THE
TWO ON THE NUMBERS OF ROW WEIGHTS OF THE READS' ROW AND OF THE TIES' ROW ARE NOT AMONG THEM): the
ties' row of the digits' array has 2 mz weights · the two lists of column sums have an entry a
matrix · the test on a tie's shapes says yes at every matrix · the plan's rows add up to mz · the
test on the planes' shapes says yes: SIX TESTS UNDER ONE "and": SAYS YES BEHIND THE ADDING. A join
of `Added8.tieShape` (Johnson/Desc/K8/Honest/TieShape.lean) and `Added8.planesShape`
(PlanesShape.lean) with two lengths that are new here. None of the library's goals.

  `eqWeights_sizes`   a yes of the run's step on the weights ⊢ the two lists of column sums have an
                   entry a matrix. ITS PROOF IS THE FIRST HALF OF THAT OF THE LIBRARY's
                   `eqWeights_spec` (Johnson/Desc/First/TailClaims/EquationsForms.lean), which drops
                   these two; the library has the like at the other text of the step
                   (`weightsF_gam`, OnBytes/Tie/Pv/Tail/EndLoopsB.lean)
  **`Added8.gamSizes`**   Added8 ⊢ tl'.gamX.size = tl'.NM ∧ tl'.gamV.size = tl'.NM: NO FURTHER
                   PREMISE
  `TiesAtY tl Y`   at the ledger behind the runs: TieArrayAt at every matrix · the ties' row has 2
                   mz weights
  `TiesPub tl`   public: ShpPub at every matrix · two matrices have two arrays · the plan's rows add
                   up to mz
  **`Added8.tiesClause`**   Added8 · nbW = tl.zzBlocks · TiesAtY · TiesPub · the claims in front and
                   the run's own are no more than the plan's number · BitsAt tl Y · BitsPub tl g ·
                   no matrix's array is the bits' ⊢ the clause, in the verifier's own letters
Limits. AN IMPLICATION. OF THE SIX TESTS TWO ARE PAID UNDER `Added8` ALONE (the two lists' lengths);
of the twenty clauses of the test on a tie's shapes eight (TieShape.lean); ALL ELSE IS CARRIED OVER
OR EXCHANGED: `TiesAtY`, `TiesPub`, `BitsAt`, `BitsPub` AND THE THREE OTHER PREMISES ARE PAID BY
NOBODY HERE. `TiesAtY` and `BitsAt` speak of the ledger behind the runs. PAYERS IN SIGHT, NOT
CALLED: the premise on the number of claims: `Added8.plan_bound` (TieShape.lean) · "no matrix's
array is the bits'": a clause of the public test `apartB` (Johnson/Desc/K8/Honest/ApartOf.lean) · of
`TiesPub`: "two matrices have two arrays" and the first of ShpPub's three equations: clauses of the
public test `symbolsLaid` (Johnson/Desc/K8/Honest/SymbolsFew.lean): so of `TiesPub` there stay K1 =
k, Kc = k and the sum.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.TieShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The two lists of column sums have an entry a matrix. -/
theorem eqWeights_sizes (tl tl1 : HTailF2) (front : Nat) (s s1 : St)
    (h : eqWeights tl front s = .ok (tl1, s1)) :
    tl1.gamX.size = tl1.NM ∧ tl1.gamV.size = tl1.NM := by
  unfold eqWeights at h
  obtain ⟨tl2, t, g1, g2⟩ := (eq_bind_ok _ _ _ _ _).1 h
  have hp := (eq_ask_ok g1).1
  have hf := (eq_get_ok g2).1
  obtain ⟨hP, -⟩ := powersF_spec tl tl2 s.1 hp
  have e1 := foldSums_fold _ _ _ hf
  obtain ⟨z1, z2, -⟩ := foldSums_fold_gam (List.range tl2.NM)
    { tl2 with gamX := Array.replicate tl2.NM #[], gamV := Array.replicate tl2.NM #[] } tl1
    (hP.vt.trans hP.vp.symm) hf
  have eN : tl1.NM = tl2.NM := by rw [e1]
  refine ⟨?_, ?_⟩
  · rw [z1, eN]
    exact Array.size_replicate ..
  · rw [z2, eN]
    exact Array.size_replicate ..

/-- At the ledger behind the runs. -/
structure TiesAtY (tl : HTailF2) (Y : Fork) : Prop where
  arrays : ∀ mu, mu < tl.NM → TieArrayAt tl Y mu
  row : ((Y.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowTies {}).L.size = 2 * tl.mz

/-- Public numbers. -/
structure TiesPub (tl : HTailF2) : Prop where
  shp : ∀ mu, mu < tl.NM → ShpPub tl mu
  inj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b
  sum : tl.shp.foldl (fun n s => n + s.m) 0 = tl.mz

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **Behind a yes of the run the two lists of column sums have an entry a matrix.** -/
theorem Added8.gamSizes (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) :
    tl'.gamX.size = tl'.NM ∧ tl'.gamV.size = tl'.NM := by
  obtain ⟨before, tla, tlb, s1, s2, arr, -, -, k9, -⟩ := eq_parts A.eq
  obtain ⟨tl1, hW, -, -, etl, -, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs _ s2 _ k9
  have h := eqWeights_sizes tlb tl1 _ s2 s2 hW
  rw [etl]
  exact h

/-- **SIX TESTS ON THE TIES' AND THE PLANES' SHAPES SAY YES BEHIND THE ADDING.** -/
theorem Added8.tiesClause (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (nbW : Nat) (hn : nbW = tl.zzBlocks) (T : TiesAtY tl Y) (P : TiesPub tl)
    (hpl : n₀ + k8.length ≤ Y.planClaimsF) (B : BitsAt tl Y) (Pb : BitsPub tl g)
    (hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.BZ) :
    ((((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size ==
        2 * tl'.mz &&
      tl'.gamX.size == tl'.NM && tl'.gamV.size == tl'.NM &&
      (List.range tl'.NM).all (tl'.tieShapeHeld (coefBody tl' g G)) &&
      tl'.shp.foldl (fun n s => n + s.m) 0 == tl'.mz &&
      tl'.planesShapeHeld (coefBody tl' g G) g) = true := by
  obtain ⟨-, -, hfr, -⟩ := A.core
  have eN : tl'.NM = tl.NM :=
    eq_same (·.NM) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eShp : tl'.shp = tl.shp :=
    eq_same (·.shp) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eMz : tl'.mz = tl.mz :=
    eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eIx : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  obtain ⟨gx, gv⟩ := A.gamSizes
  have zT : (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size =
      2 * tl'.mz := by
    have e1 : (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L =
        weightsOf G tl'.ix.ZZ (2 * nbW + 1) := weights_coefBody tl' g G _ _
    rw [e1, eIx, eMz, hn]
    show ((G.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowTies {}).L.size = _
    rw [lsize_of_frame, hfr, ← lsize_of_frame]
    exact T.row
  have hall : (List.range tl'.NM).all (tl'.tieShapeHeld (coefBody tl' g G)) = true :=
    List.all_eq_true.2 fun mu hmu => by
      have h1 : mu < tl.NM := by
        rw [← eN]
        exact List.mem_range.1 hmu
      exact A.tieShape g mu h1 (T.arrays mu h1) (P.shp mu h1) P.inj hpl
  have hsum : tl'.shp.foldl (fun n s => n + s.m) 0 = tl'.mz := by
    rw [eShp, eMz]
    exact P.sum
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨zT, gx⟩, gv⟩, hall⟩, hsum⟩, A.planesShape g B Pb hm⟩

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eqWeights_sizes
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.gamSizes
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.tiesClause
