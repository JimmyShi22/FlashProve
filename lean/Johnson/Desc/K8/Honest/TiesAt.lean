-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TiesAt.lean: WHAT THE TIES AND READS OF THE LIST "K8.equations" LAY ON ONE
ENTRY OF A MATRIX's ARRAY OF SYMBOLS; AND THAT ENTRY's WEIGHT AS TERMS IN THE BATCHING ELEMENT. A
definition, statements and proofs. On the list's own text and plain data: no block, no prover.
Lemmas; none of the library's goals.

  `eq_gamX`   a yes of the list: the columns' sums that the ties read (gamX) are `gamAt`
  `range_pick`   two sums over List.range that differ at one number alone
  `tie_symbol`   a tie's bracket at the world in which one entry of its own array of symbols is 1;
      `firstOf_step`: a matrix's equations' indices end in front of the reads'
  **`ties_at_symbol`**   tl has the powers of the element laid; mu₀ a matrix, c one of its columns;
      its array of symbols is not the digits' array, no other matrix's, and not what a read's
      vector's array reads as: the ties' and reads' terms where entry c of row 0 of that array is 1
      and all else 0, less those where all is 0, are -(theta ^ (the plan's number + the tie's first
      index) * the column's sum)
  `symTerms a tl n nf nb R mu c`   the terms of that entry's weight: the plain claims'
      (`plainTerms`), and, from the exponent n + firstOf tl mu on, the negatives of the signs of
      column c of matrix mu of the drawn matrix
  **`symTerms_ok`**   the exponents differ from each other and are at most d; **`symTerms_live`**:
      where the column has an entry other than 0, a coefficient is not 0
By: Powered.wr_val (OnBytes/Tie/Pv/Tail/EndClosed.lean) · tieRight_some, gamAt_val,
Powered.eqFirst_val (EndLoopsB.lean) · eqWeights_spec
(Johnson/Desc/First/TailClaims/EquationsForms.lean) · `readBracket_off` (WeightAt.lean) ·
`termsSum_column` (FallTerms.lean).
Limits: identities at one value of the element; from a yes alone.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.WeightAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- A yes of the list: the sums that the ties read. -/
theorem eq_gamX {n₀ : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F₁ F₂ : Fork} {k8 : List Claim}
    (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8)) :
    ∀ mu, mu < tl'.NM → tl'.gamX.getD mu #[] = gamAt tl' mu := by
  obtain ⟨before, tla, tlb, s1, s2, arr, h8, h9, k9, hcl⟩ := eq_parts h
  obtain ⟨tl1, hW, -, -, etl, -, new, hs', hlen, -⟩ :=
    eqTail_total Reading.gl allZero F₁ before tlb tl' funs n₀ s2 (F₂, arr) k9
  obtain ⟨-, -, hgam⟩ := eqWeights_spec tlb tl1 n₀ s2 s2 hW
  have e1 : tl'.gamX = tl1.gamX := (congrArg (fun z : HTailF2 => z.gamX) etl).trans rfl
  have e2 : ∀ mu, gamAt tl' mu = gamAt tl1 mu := fun mu =>
    (congrArg (fun z : HTailF2 => gamAt z mu) etl).trans rfl
  have e3 : tl'.NM = tl1.NM := (congrArg (fun z : HTailF2 => z.NM) etl).trans rfl
  intro mu hmu
  rw [e1, e2]
  exact (hgam mu (by rw [← e3]; exact hmu)).1

/-- Two sums over List.range that differ at one number alone. -/
theorem range_pick (f g : ℕ → Cb.Gl.E) (k : ℕ) : ∀ n : ℕ, k < n →
    (∀ j, j < n → j ≠ k → f j = g j) →
    ((List.range n).map f).sum - ((List.range n).map g).sum = f k - g k
  | 0, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, hk, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases e : k = n
    · subst e
      have hs : (List.range k).map f = (List.range k).map g :=
        List.map_congr_left fun j hj =>
          h j (Nat.lt_succ_of_lt (List.mem_range.1 hj)) (Nat.ne_of_lt (List.mem_range.1 hj))
      rw [hs]
      ring
    · have ih := range_pick f g k n (by omega) fun j hj hne => h j (Nat.lt_succ_of_lt hj) hne
      rw [h n (Nat.lt_succ_self n) (fun e' => e e'.symm)]
      linear_combination ih

/-- A tie's bracket where one entry of its own array of symbols is 1. -/
theorem tie_symbol (tl : HTailF2) (θ : E) (hP : Powered tl θ) (mu c : Nat) (hmu : mu < tl.NM)
    (hc : c < (tl.shp.getD mu {}).k)
    (hg : (tl.gamX.getD mu #[]).size = (tl.shp.getD mu {}).k)
    (hZ : tl.ix.ZZ ≠ tl.gtTree.getD mu 0) :
    tieBracket Reading.gl (oneAt (tl.gtTree.getD mu 0) 0 c) tl mu -
        tieBracket Reading.gl allZero tl mu =
      -Reading.gl.val ((tl.gamX.getD mu #[]).getD c zeroE) := by
  obtain ⟨wr, hwr⟩ := hP.tieRight_some mu hmu hg
  have hv := hP.wr_val Reading.gl mu hmu (hP.lt_shp mu hmu) wr hwr c hc
  have hJ := (hP.shape mu hmu).1
  unfold tieBracket
  rw [hwr]
  simp only [Option.getD_some, entry_off (tl.gtTree.getD mu 0) 0 c _ hZ, entry_zero, mul_zero,
    runSum_zero]
  rw [runSum_pick _ _ c (by rw [hJ, Nat.one_mul]; exact hc) (fun d _ hne => by
    show _ * (if tl.gtTree.getD mu 0 = tl.gtTree.getD mu 0 ∧ 0 = 0 ∧ d = c then
      (1 : Cb.Gl.E) else 0) = 0
    rw [if_neg (fun h => hne h.2.2), mul_zero])]
  have h1 : (oneAt (tl.gtTree.getD mu 0) 0 c).entry (tl.gtTree.getD mu 0) 0 c = 1 := by
    show (if tl.gtTree.getD mu 0 = tl.gtTree.getD mu 0 ∧ 0 = 0 ∧ c = c then
      (1 : Cb.Gl.E) else 0) = 1
    rw [if_pos ⟨rfl, rfl, rfl⟩]
  rw [h1, hv]
  ring

/-- **What the ties and reads lay on one symbol's entry.** -/
theorem ties_at_symbol (tl : HTailF2) (F0 : Fork) (hP : Powered tl F0.theta)
    (funs : Array HFun) (mu₀ c : Nat) (hmu : mu₀ < tl.NM) (hc : c < (tl.mats.getD mu₀ {}).k)
    (hk : (tl.shp.getD mu₀ {}).k = (tl.mats.getD mu₀ {}).k)
    (hgX : tl.gamX.getD mu₀ #[] = gamAt tl mu₀)
    (hZ : tl.ix.ZZ ≠ tl.gtTree.getD mu₀ 0)
    (hdist : ∀ mu, mu < tl.NM → mu ≠ mu₀ → tl.gtTree.getD mu 0 ≠ tl.gtTree.getD mu₀ 0)
    (hU0 : (tl.ix.U.getD 0 none).getD 0 ≠ tl.gtTree.getD mu₀ 0)
    (hU2 : (tl.ix.U.getD 2 none).getD 0 ≠ tl.gtTree.getD mu₀ 0) :
    (((List.range tl.NM).map
          (tieTerm Reading.gl (oneAt (tl.gtTree.getD mu₀ 0) 0 c) tl F0)).sum +
        sumFrom (readTerm Reading.gl (oneAt (tl.gtTree.getD mu₀ 0) 0 c) tl F0) 0
          (readsList tl funs)) -
      (((List.range tl.NM).map (tieTerm Reading.gl allZero tl F0)).sum +
        sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs)) =
      -(Reading.gl.val F0.theta ^ (F0.planClaimsF + tl.eqFirst.getD mu₀ 0) *
        Reading.gl.val ((gamAt tl mu₀).getD c zeroE)) := by
  have hr : sumFrom (readTerm Reading.gl (oneAt (tl.gtTree.getD mu₀ 0) 0 c) tl F0) 0
        (readsList tl funs) -
      sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs) = 0 := by
    rw [sumFrom_sub]
    refine sumFrom_none _ _ _ fun j z hj => ?_
    have hU : (tl.ix.U.getD z.1.tree none).getD 0 ≠ tl.gtTree.getD mu₀ 0 := by
      rcases tree_of_mem tl funs z (List.mem_of_getElem? hj) with e | e
      · rw [e]
        exact hU0
      · rw [e]
        exact hU2
    unfold readTerm
    rw [readBracket_off tl F0 z _ 0 c (fun h => hZ h.1) hU, sub_self]
  have hsz : (tl.gamX.getD mu₀ #[]).size = (tl.shp.getD mu₀ {}).k := by
    rw [hgX, hk]
    simp [gamAt]
  have ht := range_pick (tieTerm Reading.gl (oneAt (tl.gtTree.getD mu₀ 0) 0 c) tl F0)
    (tieTerm Reading.gl allZero tl F0) mu₀ tl.NM hmu (fun mu hm hne => by
      unfold tieTerm
      rw [tieBracket_off tl mu _ 0 c (fun h => hZ h.1) (fun h => hdist mu hm hne h.1)])
  have hb := tie_symbol tl F0.theta hP mu₀ c hmu (by rw [hk]; exact hc) hsz hZ
  rw [hgX] at hb
  have ht' : tieTerm Reading.gl (oneAt (tl.gtTree.getD mu₀ 0) 0 c) tl F0 mu₀ -
      tieTerm Reading.gl allZero tl F0 mu₀ =
      -(Reading.gl.val F0.theta ^ (F0.planClaimsF + tl.eqFirst.getD mu₀ 0) *
        Reading.gl.val ((gamAt tl mu₀).getD c zeroE)) := by
    unfold tieTerm
    rw [← mul_sub, hb]
    ring
  linear_combination ht + hr + ht'

/-- The terms of the weight of entry c of row 0 of matrix mu's array of symbols. -/
def symTerms (a : Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R mu c : Nat) : List (ℕ × Cb.Gl.E) :=
  plainTerms a nf nb (tl.NM + R) ++
    fromOn (fun j => - signOf (K := Cb.Gl.E) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau +
        (j - (n + firstOf tl mu))) 0))
      tl.tau (n + firstOf tl mu)

/-- A matrix's equations' indices end in front of the reads'. -/
theorem firstOf_step (tl : HTailF2) (mu : Nat) (hmu : mu < tl.NM) :
    firstOf tl mu + tl.stepF ≤ firstOf tl tl.NM := by
  unfold firstOf
  have h1 : ∑ nu ∈ Finset.range (mu + 1), tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS ≤
      ∑ nu ∈ Finset.range tl.NM, tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hmu)
  rw [Finset.sum_range_succ] at h1
  have h2 : tl.stepF ≤ tl.stepF * 2 ^ clog2 (tl.shp.getD mu {}).mS :=
    Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (by positivity))
  omega

/-- **The exponents differ from each other and are at most d.** -/
theorem symTerms_ok (a : Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R mu c d : Nat)
    (hcl : nf + (4 + (tl.NM + R)) + nb ≤ n) (hmu : mu < tl.NM)
    (hd : n + (firstOf tl tl.NM + R * tl.stepF) ≤ d + 1) :
    K9L.TermsOk (symTerms a tl n nf nb R mu c) d := by
  have h3 : tl.tau ≤ tl.stepF := K9L.le_pow_clog2 tl.tau
  have h4 := firstOf_step tl mu hmu
  obtain ⟨p1, p2⟩ := plainTerms_ok a nf nb (tl.NM + R) d (by omega)
  have pb : ∀ y ∈ plainTerms a nf nb (tl.NM + R), y.1 < n := by
    intro y hy
    unfold plainTerms at hy
    rcases List.mem_append.1 hy with hy | hy
    · have b1 := fromOn_mem _ _ _ y hy
      omega
    · have b1 := fromOn_mem _ _ _ y hy
      omega
  refine ⟨?_, ?_⟩
  · unfold symTerms
    rw [List.map_append, List.nodup_append]
    refine ⟨p1, fromOn_nodup _ _ _, ?_⟩
    intro u hu v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    have b1 := pb y hy
    have b2 := fromOn_mem _ _ _ z hz
    omega
  · intro y hy
    unfold symTerms at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact p2 y hy
    · have b1 := fromOn_mem _ _ _ y hy
      omega

/-- **Where the column has an entry other than 0, a coefficient is not 0.** -/
theorem symTerms_live (a : Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R mu c : Nat)
    (h : columnLive tl mu c = true) : ∃ y ∈ symTerms a tl n nf nb R mu c, y.2 ≠ 0 := by
  simp only [columnLive, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨u, hu, hne⟩ := h
  refine ⟨_, List.mem_append_right _ (fromOn_has _ tl.tau (n + firstOf tl mu)
    (n + firstOf tl mu + u) (by omega) (by omega)), ?_⟩
  simp only [Nat.add_sub_cancel_left]
  exact neg_ne_zero.2 (signOf_ne _ hne)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.eq_gamX
#print axioms VerifiableInference.Desc.First.K8.Honest.range_pick
#print axioms VerifiableInference.Desc.First.K8.Honest.tie_symbol
#print axioms VerifiableInference.Desc.First.K8.Honest.ties_at_symbol
#print axioms VerifiableInference.Desc.First.K8.Honest.firstOf_step
#print axioms VerifiableInference.Desc.First.K8.Honest.symTerms_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.symTerms_live
