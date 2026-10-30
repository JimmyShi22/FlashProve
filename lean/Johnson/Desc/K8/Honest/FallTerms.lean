-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallTerms.lean: THE WEIGHT OF AN ENTRY OF THE VECTOR OF READS AS A POLYNOMIAL IN
THE BATCHING ELEMENT, GIVEN BY ITS TERMS. A definition, statements and proofs, for the count of
Johnson/Desc/K8/Honest/FallCount.lean. On ledgers, lists of claims and plain data: no block, no
prover.

  `unitTerms a tl n nf nb R K pos q mu c`   the terms (exponent, coefficient) of the weight of the
      entry of place pos: the plain claims in front (numbers 0 .. nf + 3) and behind the smallness
      test's ties and reads, with the coefficients a; and, from the exponent
      n + (the first read's index) + q * stepF on, the negatives of the signs of column c of matrix
      mu of the drawn matrix. n: the plan's number of claims; q: the read's number; R: how many
      reads there are; K: the columns of the vector's array.
  `termsSum_append`, `termsSum_fromOn`, `termsSum_column`, `fromOn_has`
  **`unitTerms_ok`**   the exponents differ from each other and are at most d
  **`unitTerms_live`**   where the column has an entry other than 0, a coefficient is not 0
  **`weight_terms`**   behind the adding of nf plain claims, the list "K8.equations" and nb plain
      claims to a ledger that is worth 0 in every world, the weight of the entry is these terms' sum
      at the element
Limits: `weight_terms` from a yes of the list and of the adding alone; a is a letter.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallReads
import Johnson.Desc.First.Batch.Law.AtBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port
open OnBytes.Tie.Pv.Tail (PlacesApart)

/-- The terms of the weight of the entry of place pos. -/
def unitTerms (a : Nat → Nat → Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R K pos q mu c : Nat) :
    List (ℕ × Cb.Gl.E) :=
  fromOn (fun j => a j (pos / K) (pos % K)) (nf + 4) 0 ++
    fromOn (fun j => a j (pos / K) (pos % K)) nb (nf + (4 + (tl.NM + R))) ++
    fromOn (fun j => - signOf (K := Cb.Gl.E) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau +
        (j - (n + (firstOf tl tl.NM + q * tl.stepF)))) 0))
      tl.tau (n + (firstOf tl tl.NM + q * tl.stepF))

theorem termsSum_append (l l' : List (ℕ × Cb.Gl.E)) (x : Cb.Gl.E) :
    K9L.termsSum (l ++ l') x = K9L.termsSum l x + K9L.termsSum l' x := by
  simp [K9L.termsSum]

theorem termsSum_fromOn (a : Nat → Cb.Gl.E) (x : Cb.Gl.E) : ∀ (m c : Nat),
    K9L.termsSum (fromOn a m c) x = runSum (fun j => x ^ j * a j) m c
  | 0, _ => by simp [fromOn, K9L.termsSum, runSum]
  | m + 1, c => by
    simp only [fromOn, K9L.termsSum, List.map_cons, List.sum_cons, runSum]
    rw [← termsSum_fromOn a x m (c + 1)]
    rfl

theorem termsSum_column (tl : HTailF2) (x : Cb.Gl.E) (e mu c : Nat) :
    K9L.termsSum (fromOn (fun j => - signOf (K := Cb.Gl.E)
        (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + (j - e)) 0)) tl.tau e) x =
      -(x ^ e * ∑ u ∈ Finset.range tl.tau,
        signOf (K := Cb.Gl.E) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0) * x ^ u) := by
  rw [termsSum_fromOn, runSum_eq_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  simp only [Nat.add_sub_cancel_left, pow_add]
  ring

theorem fromOn_has (a : Nat → Cb.Gl.E) : ∀ (m c j : Nat), c ≤ j → j < c + m →
    (j, a j) ∈ fromOn a m c
  | 0, c, j, h1, h2 => by omega
  | m + 1, c, j, h1, h2 => by
    simp only [fromOn, List.mem_cons]
    by_cases e : j = c
    · left
      rw [e]
    · right
      exact fromOn_has a m (c + 1) j (by omega) (by omega)

/-- **The exponents differ from each other and are at most d.** -/
theorem unitTerms_ok (a : Nat → Nat → Nat → Cb.Gl.E) (tl : HTailF2)
    (n nf nb R K pos q mu c d : Nat) (hcl : nf + (4 + (tl.NM + R)) + nb ≤ n) (hq : q < R)
    (hd : n + (firstOf tl tl.NM + R * tl.stepF) ≤ d + 1) :
    K9L.TermsOk (unitTerms a tl n nf nb R K pos q mu c) d := by
  have h1 : (q + 1) * tl.stepF ≤ R * tl.stepF := Nat.mul_le_mul_right _ hq
  have h2 : (q + 1) * tl.stepF = q * tl.stepF + tl.stepF := Nat.succ_mul _ _
  have h3 : tl.tau ≤ tl.stepF := K9L.le_pow_clog2 tl.tau
  refine ⟨?_, ?_⟩
  · unfold unitTerms
    rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
    refine ⟨⟨fromOn_nodup _ _ _, fromOn_nodup _ _ _, ?_⟩, fromOn_nodup _ _ _, ?_⟩
    · intro u hu v hv
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
      have b1 := fromOn_mem _ _ _ y hy
      have b2 := fromOn_mem _ _ _ z hz
      omega
    · intro u hu v hv
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
      have b2 := fromOn_mem _ _ _ z hz
      rcases List.mem_append.1 hu with hu | hu
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
        have b1 := fromOn_mem _ _ _ y hy
        omega
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
        have b1 := fromOn_mem _ _ _ y hy
        omega
  · intro y hy
    unfold unitTerms at hy
    rcases List.mem_append.1 hy with hy | hy
    · rcases List.mem_append.1 hy with hy | hy
      · have b1 := fromOn_mem _ _ _ y hy
        omega
      · have b1 := fromOn_mem _ _ _ y hy
        omega
    · have b1 := fromOn_mem _ _ _ y hy
      omega

theorem signOf_ne (z : Int) (h : z ≠ 0) : signOf (K := Cb.Gl.E) z ≠ 0 := by
  unfold signOf
  rw [if_neg h]
  split
  · exact neg_ne_zero.2 one_ne_zero
  · exact one_ne_zero

/-- **Where the column has an entry other than 0, a coefficient is not 0.** -/
theorem unitTerms_live (a : Nat → Nat → Nat → Cb.Gl.E) (tl : HTailF2)
    (n nf nb R K pos q mu c : Nat) (h : columnLive tl mu c = true) :
    ∃ y ∈ unitTerms a tl n nf nb R K pos q mu c, y.2 ≠ 0 := by
  simp only [columnLive, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨u, hu, hne⟩ := h
  refine ⟨_, List.mem_append_right _ (fromOn_has _ tl.tau (n + (firstOf tl tl.NM + q * tl.stepF))
    (n + (firstOf tl tl.NM + q * tl.stepF) + u) (by omega) (by omega)), ?_⟩
  simp only [Nat.add_sub_cancel_left]
  exact neg_ne_zero.2 (signOf_ne _ hne)

/-- **What the ledger behind the adding lays on the entry of place pos, as its terms' sum.** Said of
the ledger's value where that entry is 1 and all else 0, less its value where all is 0
(`total_oneAt`: that is the weight on the entry). Y: the ledger to which the list is added, worth 0
in every world; G: the ledger behind the adding; F₁: the ledger at which "K8.equations" is made. -/
theorem weight_terms (a : Nat → Nat → Nat → Cb.Gl.E) (tl tl' : HTailF2) (funs : Array HFun)
    (Y G F₁ F₂ : Fork) (fr k8 bk : List Claim) (n₀ tU nf nb pos q c : Nat) (y : HFun × Nat)
    (hadd : addAll Y (fr ++ k8 ++ bk) = some G)
    (hz : ∀ W : World Cb.Gl.E, Y.total Reading.gl W = 0) (hn0 : Y.nClaim = 0)
    (hsz : Y.LS.size = Y.ns)
    (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (hth : F₁.theta = Y.theta) (hpl : F₁.planClaimsF = Y.planClaimsF)
    (hfr : treesFrame F₁.trees = treesFrame Y.trees)
    (hnf : fr.length = nf) (hnb : bk.length = nb)
    (hA : ∀ j cl, (fr ++ k8.take 4)[j]? = some cl →
      cl.eqFirst = none ∧ ∀ r i, coefOn cl tU r i = a j r i)
    (hB : ∀ j cl, bk[j]? = some cl →
      cl.eqFirst = none ∧ ∀ r i, coefOn cl tU r i = a (nf + k8.length + j) r i)
    (hZ : tl.ix.ZZ ≠ tU) (hg : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tU)
    (hU0 : tl.ix.U.getD 0 none = none) (hU2 : tl.ix.U.getD 2 none = some tU)
    (hq : (readsList tl funs)[q]? = some y) (hc : c < (tl.mats.getD y.1.mat {}).k)
    (hpos : posOf tl y.1 y.2 c = pos) :
    G.total Reading.gl (oneAt tU (pos / colsU F₁ tU) (pos % colsU F₁ tU)) -
        G.total Reading.gl allZero =
      K9L.termsSum (unitTerms a tl Y.planClaimsF nf nb (readsList tl funs).length (colsU F₁ tU)
        pos q y.1.mat c) (Reading.gl.val Y.theta) := by
  obtain ⟨tl1, hP, hgam, etl, h4, hk8, hpush⟩ := k8_cut h
  -- the conditions, and the terms, at the data with the powers laid
  have hcond : (tl1.ix.ZZ ≠ tU ∧ (∀ mu, mu < tl1.NM → tl1.gtTree.getD mu 0 ≠ tU) ∧
      tl1.ix.U.getD 0 none = none ∧ tl1.ix.U.getD 2 none = some tU ∧
      (readsList tl1 funs)[q]? = some y ∧ c < (tl1.mats.getD y.1.mat {}).k ∧
      posOf tl1 y.1 y.2 c = pos) :=
    (same1 (fun t : HTailF2 => (t.ix.ZZ ≠ tU ∧ (∀ mu, mu < t.NM → t.gtTree.getD mu 0 ≠ tU) ∧
      t.ix.U.getD 0 none = none ∧ t.ix.U.getD 2 none = some tU ∧
      (readsList t funs)[q]? = some y ∧ c < (t.mats.getD y.1.mat {}).k ∧
      posOf t y.1 y.2 c = pos)) h etl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)).mpr ⟨hZ, hg, hU0, hU2, hq, hc, hpos⟩
  obtain ⟨hZ1, hg1, hU01, hU21, hq1, hc1, hpos1⟩ := hcond
  rw [← same1 (fun t : HTailF2 => unitTerms a t Y.planClaimsF nf nb (readsList tl funs).length
    (colsU F₁ tU) pos q y.1.mat c) h etl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)]
  have eNM : tl1.NM = tl.NM :=
    same1 (fun t => t.NM) h etl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have t1 : ∀ {α : Type} (f : HTailF2 → α), (∀ (t : HTailF2) (x y : Array Nat) (z : Nat),
      f { t with tieObj := x, tiesOn := y, nX4Laid := z } = f t) → f tl' = f tl1 :=
    fun f r => (congrArg f etl).trans (r _ _ _ _)
  obtain ⟨hap', hcol'⟩ := eq_apart n₀ tl tl' funs F₁ F₂ k8 h
  have hap : (readsList tl1 funs).Pairwise (PlacesApart tl1) :=
    (t1 (fun t => (readsList t funs).Pairwise (PlacesApart t)) (fun _ _ _ _ => rfl)).mp hap'
  have hcol : ∀ x ∈ readsList tl1 funs, ∀ d d', d < d' → d' < (tl1.mats.getD x.1.mat {}).k →
      posOf tl1 x.1 x.2 d ≠ posOf tl1 x.1 x.2 d' :=
    (t1 (fun t => ∀ x ∈ readsList t funs, ∀ d d', d < d' → d' < (t.mats.getD x.1.mat {}).k →
      posOf t x.1 x.2 d ≠ posOf t x.1 x.2 d') (fun _ _ _ _ => rfl)).mp hcol'
  have hrd' := eq_reads n₀ tl tl' funs F₁ F₂ k8 h
  have hrd : ∀ x ∈ readsList tl1 funs, (tl1.ix.U.getD x.1.tree none).isSome = true :=
    (t1 (fun t => ∀ x ∈ readsList t funs, (t.ix.U.getD x.1.tree none).isSome = true)
      (fun _ _ _ _ => rfl)).mp (fun x hx => (hrd' x hx).1)
  have hU : ∀ x ∈ readsList tl1 funs, tl1.ix.U.getD x.1.tree none = some tU ∧ x.1.tree = 2 := by
    intro x hx
    rcases tree_of_mem tl1 funs x hx with e | e
    · have h5 := hrd x hx
      rw [e, hU01] at h5
      exact absurd h5 (by simp)
    · exact ⟨by rw [e]; exact hU21, e⟩
  have hmem : y ∈ readsList tl1 funs := List.mem_of_getElem? hq1
  have hmat : y.1.mat < tl1.NM := ((mem_readsList tl1 funs y.1 y.2).1 hmem).2.1
  -- the adding, cut in three
  have hsplit : fr ++ k8 ++ bk = (fr ++ k8.take 4) ++ (k8.drop 4 ++ bk) := by
    conv_lhs => rw [← List.take_append_drop 4 k8]
    simp only [List.append_assoc]
  rw [hsplit, addAll_append] at hadd
  cases hA1 : addAll Y (fr ++ k8.take 4) with
  | none =>
    rw [hA1] at hadd
    exact absurd hadd (by simp)
  | some A1 =>
    rw [hA1] at hadd
    change addAll A1 (k8.drop 4 ++ bk) = some G at hadd
    rw [addAll_append] at hadd
    cases hA2 : addAll A1 (k8.drop 4) with
    | none =>
      rw [hA2] at hadd
      exact absurd hadd (by simp)
    | some A2 =>
      rw [hA2] at hadd
      change addAll A2 bk = some G at hadd
      have s1 := fun W => K9L.addAll_total Reading.gl W (fr ++ k8.take 4) Y A1 hsz hA1
      obtain ⟨-, eA1, zA1, fA1⟩ := s1 allZero
      have kA1 : Kept F₁ A1 :=
        ⟨by rw [eA1]; exact hth.symm, by rw [eA1]; exact hpl.symm, zA1, fA1.trans hfr.symm⟩
      have s2 := fun W => hpush W A1 A2 kA1 hA2
      obtain ⟨kA2, nA2, -⟩ := s2 allZero
      have s3 := fun W => K9L.addAll_total Reading.gl W bk A2 G kA2.sized hadd
      have nA1 : A1.nClaim = nf + 4 := by
        rw [eA1]
        show Y.nClaim + (fr ++ k8.take 4).length = nf + 4
        rw [hn0, List.length_append, hnf, h4, Nat.zero_add]
      have p1 := claimsSum_plain (Reading.gl.val Y.theta) Y.planClaimsF tU (pos / colsU F₁ tU)
        (pos % colsU F₁ tU) (fun j => a j (pos / colsU F₁ tU) (pos % colsU F₁ tU))
        (fr ++ k8.take 4) 0 (fun j cl hj => by
          obtain ⟨b1, b2⟩ := hA j cl hj
          exact ⟨b1, by rw [Nat.zero_add]; exact b2 _ _⟩)
      have p3 := claimsSum_plain (Reading.gl.val Y.theta) Y.planClaimsF tU (pos / colsU F₁ tU)
        (pos % colsU F₁ tU) (fun j => a j (pos / colsU F₁ tU) (pos % colsU F₁ tU))
        bk (nf + (4 + (tl1.NM + (readsList tl funs).length))) (fun j cl hj => by
          obtain ⟨b1, b2⟩ := hB j cl hj
          refine ⟨b1, ?_⟩
          rw [b2, hk8, eNM])
      have p2 := reads_weight tl1 F₁ funs tU pos q c y hZ1 hg1 hU hap hcol hq1 hc1 hpos1
      have gv : Reading.gl.val ((tl1.gamV.getD y.1.mat #[]).getD c zeroE) =
          ∑ u ∈ Finset.range tl1.tau, signOf (K := Cb.Gl.E)
            (tl1.cfF.getD ((tl1.cfFirst.getD y.1.mat 0 + c) * tl1.tau + u) 0) *
              Reading.gl.val F₁.theta ^ u := by
        rw [hgam y.1.mat hmat]
        exact gamAt_val Reading.gl hP y.1.mat c hc1
      have ef : tl1.eqFirst.getD tl1.NM 0 = firstOf tl1 tl1.NM :=
        hP.eqFirst_val tl1.NM hP.NM_le_shp
      rw [(s3 _).1, (s3 allZero).1, (s2 _).2.2, (s2 allZero).2.2, (s1 _).1, (s1 allZero).1,
        hz, hz, kA2.theta, kA2.plan, hth, hpl, hn0, nA2, nA1]
      unfold unitTerms
      rw [termsSum_append, termsSum_append, termsSum_column]
      rw [List.length_append, hnf, h4] at p1
      rw [hnb] at p3
      rw [gv, ef, hth, hpl] at p2
      rw [← p1, ← p3, eNM]
      rw [eNM] at p2
      have e3 : nf + 4 + (tl.NM + (readsList tl funs).length) =
          nf + (4 + (tl.NM + (readsList tl funs).length)) := by omega
      rw [e3]
      linear_combination p2

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.unitTerms_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.unitTerms_live
#print axioms VerifiableInference.Desc.First.K8.Honest.weight_terms
