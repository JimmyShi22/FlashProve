-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WeightAt.lean: WHAT THE ADDING LAYS ON ANY ONE ENTRY OF ANY ARRAY, AS TERMS
IN THE BATCHING ELEMENT. A definition, statements and proofs. On ledgers, lists of claims and plain
data: no block, no state of the chain, no prover. Lemmas; none of the library's goals.

Johnson/Desc/K8/Honest/FallTerms.lean says it of an entry of the vector of reads. Here the entry is
a letter.
  **`total_cut`**   behind the adding of nf plain claims, the list "K8.equations" and nb plain
      claims to a ledger that is worth 0 in every world: the ledger's value where entry i of virtual
      row r of array t is 1 and all else 0, less its value where all is 0, is: the plain claims'
      terms at the element, and what the list's ties and reads part by in the two worlds. a j: the
      coefficient of plain claim number j on the entry
  `OffAt tl t r`   virtual row r of array t is none of those on which the ties and reads lay a
      weight: not the ties' and not the reads' row of the digits' array, not row 0 of a matrix's
      array of symbols, and t is not what the array of a vector that a read names reads as
  `entry_off_row`, `tieBracket_off`, `readBracket_off`, **`brackets_off`**   the ties and reads part
      by nothing at such a row
  `plainTerms a nf nb M`   the plain claims' terms: (j, a j) for j < nf + 4 and for nf + (4 + M) ≤ j
      < nf + (4 + M) + nb; `plainTerms_ok`: the exponents differ and are at most d;
      `plainTerms_live`: a coefficient is not 0 if one of the first nf + 4 is not
  **`plain_weight`**   so at such a row the difference is the plain claims' terms' sum
By: `k8_cut`, `same1` (FallReads.lean) · tree_of_mem
(Johnson/Desc/First/TailClaims/EquationsCover.lean) · `claimsSum_plain` (FallAlg.lean) ·
K9L.addAll_total.
Limits: from a yes of the list and of the adding alone; a is a letter. The difference is the weight
that a test reads only where the virtual row's weights begin at column 0 (`total_oneAt`).
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **The adding, cut in three, at any entry.** -/
theorem total_cut (a : Nat → Cb.Gl.E) (tl tl' : HTailF2) (funs : Array HFun)
    (Y G F₁ F₂ : Fork) (fr k8 bk : List Claim) (n₀ t r i nf nb : Nat)
    (hadd : addAll Y (fr ++ k8 ++ bk) = some G)
    (hz : ∀ W : World Cb.Gl.E, Y.total Reading.gl W = 0) (hn0 : Y.nClaim = 0)
    (hsz : Y.LS.size = Y.ns)
    (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (hth : F₁.theta = Y.theta) (hpl : F₁.planClaimsF = Y.planClaimsF)
    (hfr : treesFrame F₁.trees = treesFrame Y.trees)
    (hnf : fr.length = nf) (hnb : bk.length = nb)
    (hA : ∀ j cl, (fr ++ k8.take 4)[j]? = some cl → cl.eqFirst = none ∧ coefOn cl t r i = a j)
    (hB : ∀ j cl, bk[j]? = some cl →
      cl.eqFirst = none ∧ coefOn cl t r i = a (nf + k8.length + j)) :
    ∃ tl1 : HTailF2, Powered tl1 F₁.theta ∧
      (∀ mu, mu < tl1.NM → tl1.gamV.getD mu #[] = gamAt tl1 mu) ∧
      tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid } ∧
      G.total Reading.gl (oneAt t r i) - G.total Reading.gl allZero =
        K9L.termsSum (fromOn a (nf + 4) 0) (Reading.gl.val Y.theta) +
        K9L.termsSum (fromOn a nb (nf + (4 + (tl.NM + (readsList tl funs).length))))
          (Reading.gl.val Y.theta) +
        ((((List.range tl1.NM).map (tieTerm Reading.gl (oneAt t r i) tl1 F₁)).sum +
            sumFrom (readTerm Reading.gl (oneAt t r i) tl1 F₁) 0 (readsList tl1 funs)) -
          (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
            sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs))) := by
  obtain ⟨tl1, hP, hgam, etl, h4, hk8, hpush⟩ := k8_cut h
  refine ⟨tl1, hP, hgam, etl, ?_⟩
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
      have p1 := claimsSum_plain (Reading.gl.val Y.theta) Y.planClaimsF t r i a
        (fr ++ k8.take 4) 0 (fun j cl hj => by
          obtain ⟨b1, b2⟩ := hA j cl hj
          exact ⟨b1, by rw [Nat.zero_add]; exact b2⟩)
      have p3 := claimsSum_plain (Reading.gl.val Y.theta) Y.planClaimsF t r i a
        bk (nf + (4 + (tl.NM + (readsList tl funs).length))) (fun j cl hj => by
          obtain ⟨b1, b2⟩ := hB j cl hj
          refine ⟨b1, ?_⟩
          rw [b2, hk8])
      rw [(s3 _).1, (s3 allZero).1, (s2 _).2.2, (s2 allZero).2.2, (s1 _).1, (s1 allZero).1,
        hz, hz, kA2.theta, kA2.plan, hth, hpl, hn0, nA2, nA1]
      rw [List.length_append, hnf, h4] at p1
      rw [hnb] at p3
      rw [← p1, ← p3]
      have e3 : nf + 4 + (tl.NM + (readsList tl funs).length) =
          nf + (4 + (tl.NM + (readsList tl funs).length)) := by omega
      rw [e3]
      ring

/-- The world `oneAt` at another virtual row. -/
theorem entry_off_row (t r i t' r' i' : Nat) (h : ¬ (t' = t ∧ r' = r)) :
    (oneAt t r i).entry t' r' i' = 0 := by
  show (if t' = t ∧ r' = r ∧ i' = i then (1 : Cb.Gl.E) else 0) = 0
  rw [if_neg fun hc => h ⟨hc.1, hc.2.1⟩]

/-- **Virtual row r of array t is none of those on which the ties and reads lay a weight**: not the
ties' row and not the reads' row of the digits' array; not row 0 of a matrix's array of symbols; t
is not what the array of a vector that a read names reads as. -/
def OffAt (tl : HTailF2) (t r : Nat) : Prop :=
  ¬ (tl.ix.ZZ = t ∧ tl.zzRowTies = r) ∧ ¬ (tl.ix.ZZ = t ∧ tl.zzRowReads = r) ∧
    (∀ mu, mu < tl.NM → ¬ (tl.gtTree.getD mu 0 = t ∧ 0 = r)) ∧
    (tl.ix.U.getD 0 none).getD 0 ≠ t ∧ (tl.ix.U.getD 2 none).getD 0 ≠ t

theorem tieBracket_off (tl : HTailF2) (mu t r i : Nat)
    (hT : ¬ (tl.ix.ZZ = t ∧ tl.zzRowTies = r)) (hg : ¬ (tl.gtTree.getD mu 0 = t ∧ 0 = r)) :
    tieBracket Reading.gl (oneAt t r i) tl mu = tieBracket Reading.gl allZero tl mu := by
  unfold tieBracket
  simp only [entry_off_row t r i _ _ _ hT, entry_off_row t r i _ _ _ hg, entry_zero]

theorem readBracket_off (tl : HTailF2) (F0 : Fork) (x : HFun × Nat) (t r i : Nat)
    (hR : ¬ (tl.ix.ZZ = t ∧ tl.zzRowReads = r))
    (hU : (tl.ix.U.getD x.1.tree none).getD 0 ≠ t) :
    readBracket Reading.gl (oneAt t r i) tl F0 x = readBracket Reading.gl allZero tl F0 x := by
  unfold readBracket
  simp only [entry_off_row t r i _ _ _ hR, entry_off t r i _ hU, entry_zero]

/-- **The ties and reads lay nothing on such a row.** -/
theorem brackets_off (tl : HTailF2) (F0 : Fork) (funs : Array HFun) (t r i : Nat)
    (h : OffAt tl t r) :
    (((List.range tl.NM).map (tieTerm Reading.gl (oneAt t r i) tl F0)).sum +
        sumFrom (readTerm Reading.gl (oneAt t r i) tl F0) 0 (readsList tl funs)) -
      (((List.range tl.NM).map (tieTerm Reading.gl allZero tl F0)).sum +
        sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs)) = 0 := by
  obtain ⟨hT, hR, hg, hU0, hU2⟩ := h
  have ht : (List.range tl.NM).map (tieTerm Reading.gl (oneAt t r i) tl F0) =
      (List.range tl.NM).map (tieTerm Reading.gl allZero tl F0) :=
    List.map_congr_left fun mu hmu => by
      unfold tieTerm
      rw [tieBracket_off tl mu t _ _ hT (hg mu (List.mem_range.1 hmu))]
  have hr : sumFrom (readTerm Reading.gl (oneAt t r i) tl F0) 0 (readsList tl funs) -
      sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs) = 0 := by
    rw [sumFrom_sub]
    refine sumFrom_none _ _ _ fun j z hj => ?_
    have hU : (tl.ix.U.getD z.1.tree none).getD 0 ≠ t := by
      rcases tree_of_mem tl funs z (List.mem_of_getElem? hj) with e | e
      · rw [e]
        exact hU0
      · rw [e]
        exact hU2
    unfold readTerm
    rw [readBracket_off tl F0 z t r i hR hU, sub_self]
  rw [ht]
  linear_combination hr

/-- The plain claims' terms. -/
def plainTerms (a : Nat → Cb.Gl.E) (nf nb M : Nat) : List (ℕ × Cb.Gl.E) :=
  fromOn a (nf + 4) 0 ++ fromOn a nb (nf + (4 + M))

theorem plainTerms_ok (a : Nat → Cb.Gl.E) (nf nb M d : Nat) (hd : nf + (4 + M) + nb ≤ d + 1) :
    K9L.TermsOk (plainTerms a nf nb M) d := by
  unfold plainTerms
  refine ⟨?_, fun y hy => ?_⟩
  · rw [List.map_append, List.nodup_append]
    refine ⟨fromOn_nodup a _ _, fromOn_nodup a _ _, fun u hu v hv => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hv
    have h1 := fromOn_mem a _ _ y hy
    have h2 := fromOn_mem a _ _ z hz
    omega
  · rcases List.mem_append.1 hy with h | h
    · have h1 := fromOn_mem a _ _ y h
      omega
    · have h1 := fromOn_mem a _ _ y h
      omega

theorem plainTerms_live (a : Nat → Cb.Gl.E) (nf nb M j : Nat) (hj : j < nf + 4) (ha : a j ≠ 0) :
    ∃ y ∈ plainTerms a nf nb M, y.2 ≠ 0 :=
  ⟨(j, a j), List.mem_append_left _ (fromOn_has a (nf + 4) 0 j (Nat.zero_le _) (by omega)), ha⟩

/-- **The weight of an entry of an array that is none of the ties' and reads'.** -/
theorem plain_weight (a : Nat → Cb.Gl.E) (tl tl' : HTailF2) (funs : Array HFun)
    (Y G F₁ F₂ : Fork) (fr k8 bk : List Claim) (n₀ t r i nf nb : Nat)
    (hadd : addAll Y (fr ++ k8 ++ bk) = some G)
    (hz : ∀ W : World Cb.Gl.E, Y.total Reading.gl W = 0) (hn0 : Y.nClaim = 0)
    (hsz : Y.LS.size = Y.ns)
    (h : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (hth : F₁.theta = Y.theta) (hpl : F₁.planClaimsF = Y.planClaimsF)
    (hfr : treesFrame F₁.trees = treesFrame Y.trees)
    (hnf : fr.length = nf) (hnb : bk.length = nb)
    (hA : ∀ j cl, (fr ++ k8.take 4)[j]? = some cl → cl.eqFirst = none ∧ coefOn cl t r i = a j)
    (hB : ∀ j cl, bk[j]? = some cl →
      cl.eqFirst = none ∧ coefOn cl t r i = a (nf + k8.length + j))
    (hoff : OffAt tl t r) :
    G.total Reading.gl (oneAt t r i) - G.total Reading.gl allZero =
      K9L.termsSum (plainTerms a nf nb (tl.NM + (readsList tl funs).length))
        (Reading.gl.val Y.theta) := by
  obtain ⟨tl1, -, -, etl, hcut⟩ := total_cut a tl tl' funs Y G F₁ F₂ fr k8 bk n₀ t r i nf nb hadd
    hz hn0 hsz h hth hpl hfr hnf hnb hA hB
  have hcond : OffAt tl1 t r :=
    (same1 (fun u : HTailF2 => OffAt u t r) h etl (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)).mpr hoff
  rw [hcut, brackets_off tl1 F₁ funs t r i hcond, add_zero]
  unfold plainTerms
  rw [termsSum_append]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.total_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.brackets_off
#print axioms VerifiableInference.Desc.First.K8.Honest.plainTerms_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.plainTerms_live
#print axioms VerifiableInference.Desc.First.K8.Honest.plain_weight
