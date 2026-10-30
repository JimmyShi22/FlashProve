-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontCount.lean: THE SMALLNESS TEST: AT HOW MANY VALUES OF THE
BATCHING ELEMENT A COLUMN OF THE DRAWN MATRIX HAS THE WEIGHT 0. Definitions with code, statements
and proofs, at the text of Johnson/Desc/ProofFile/Honest/K8/Share.lean (`columnWeight`,
`zeroColumnWeight`, `k8Front`). No prover. LEMMAS; NONE OF THE LIBRARY's GOALS. NOTHING IS CLAIMED
ON COMPLETENESS, SOUNDNESS OR HIDING.

A column's weight at chi is the sum over u of chi^u times the sign of the column's entry number u: a
polynomial in chi of a degree below tau, and not the zero polynomial where the column has an entry
other than 0.
  `allLive tl`   WITH CODE: every column of every matrix has an entry other than 0
  `cols tl`      the columns of all matrices
  `columnWeight_val`   the weight, read in the field
  `colTerms`, `colTerms_sum`, `colTerms_ok`, `colTerms_live`   the polynomial by its terms
  **`front_few`**   allLive tl gives: at most cols tl * (tau - 1) field elements are values of chi
      at which `zeroColumnWeight` finds a column
  **`k8Front_few`**   the same at `k8Front`, at a state that holds tl
Limits. At data with a column that is all 0 nothing is said (there every value of chi is such a
value): how often that is: Johnson/Desc/K8/Honest/DeadColumn.lean. The count is of field elements,
each as the reduced words `chiAt` gives. `zeroColumnWeight` runs over all columns of all matrices.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.Share
import Johnson.Desc.K8.Honest.FallTerms
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Tie.Pv.Tail.Port

/-- Every column of every matrix of the drawn matrix has an entry other than 0. -/
def allLive (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu =>
    (List.range (tl.mats.getD mu {}).k).all fun c => columnLive tl mu c

/-- The columns of all matrices. -/
def cols (tl : HTailF2) : Nat := ∑ mu ∈ Finset.range tl.NM, (tl.mats.getD mu {}).k

/-- The weight of a column, read in the field. -/
theorem columnWeight_val (tl : HTailF2) (chi : E) (mu c : Nat) :
    Reading.gl.val (columnWeight tl chi mu c) =
      ∑ u ∈ Finset.range tl.tau, signOf (K := Cb.Gl.E)
        (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0) * Reading.gl.val chi ^ u := by
  unfold columnWeight
  rw [foldColumn_val Reading.gl _ _ _ _ (powers_size chi tl.tau)]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [powers_val Reading.gl chi tl.tau u (Finset.mem_range.1 hu)]

/-- The terms of a column's weight: (u, the sign of entry number u). -/
def colTerms (tl : HTailF2) (mu c : Nat) : List (ℕ × Cb.Gl.E) :=
  fromOn (fun u => signOf (K := Cb.Gl.E) (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0))
    tl.tau 0

theorem colTerms_sum (tl : HTailF2) (mu c : Nat) (x : Cb.Gl.E) :
    K9L.termsSum (colTerms tl mu c) x =
      ∑ u ∈ Finset.range tl.tau, signOf (K := Cb.Gl.E)
        (tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0) * x ^ u := by
  unfold colTerms
  rw [termsSum_fromOn, runSum_eq_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Nat.zero_add]
  ring

theorem colTerms_ok (tl : HTailF2) (mu c : Nat) : K9L.TermsOk (colTerms tl mu c) (tl.tau - 1) := by
  refine ⟨fromOn_nodup _ _ _, fun y hy => ?_⟩
  have b := fromOn_mem _ _ _ y hy
  omega

theorem colTerms_live (tl : HTailF2) (mu c : Nat) (h : columnLive tl mu c = true) :
    ∃ y ∈ colTerms tl mu c, y.2 ≠ 0 := by
  simp only [columnLive, List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨u, hu, hne⟩ := h
  exact ⟨_, fromOn_has _ tl.tau 0 u (Nat.zero_le u) (by omega), signOf_ne _ hne⟩

/-- **The count.** -/
theorem front_few (tl : HTailF2) (h : allLive tl = true) :
    Prob.cnt (fun x : Cb.Gl.E => (zeroColumnWeight tl (E.ofTriple (Slice.ofE x))).isSome = true) ≤
      cols tl * (tl.tau - 1) := by
  simp only [allLive, List.all_eq_true, List.mem_range] at h
  calc Prob.cnt (fun x : Cb.Gl.E =>
        (zeroColumnWeight tl (E.ofTriple (Slice.ofE x))).isSome = true)
      ≤ Prob.cnt (fun x : Cb.Gl.E => ∃ mu ∈ Finset.range tl.NM,
          ∃ c ∈ Finset.range (tl.mats.getD mu {}).k, K9L.termsSum (colTerms tl mu c) x = 0) :=
        Prob.cnt_mono fun x hx => by
          obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hx
          unfold zeroColumnWeight at hq
          obtain ⟨mu, hmu, h1⟩ := List.exists_of_findSome?_eq_some hq
          obtain ⟨c, hc, h2⟩ := List.exists_of_findSome?_eq_some h1
          refine ⟨mu, Finset.mem_range.2 (List.mem_range.1 hmu), c,
            Finset.mem_range.2 (List.mem_range.1 hc), ?_⟩
          split at h2
          · rename_i hz
            have hv := columnWeight_val tl (E.ofTriple (Slice.ofE x)) mu c
            rw [isZeroE_eq hz, Reading.gl.zero] at hv
            have hx' : Reading.gl.val (E.ofTriple (Slice.ofE x)) = x := Slice.toE_ofE x
            rw [hx'] at hv
            rw [colTerms_sum, ← hv]
          · cases h2
    _ ≤ ∑ mu ∈ Finset.range tl.NM, Prob.cnt (fun x : Cb.Gl.E =>
          ∃ c ∈ Finset.range (tl.mats.getD mu {}).k, K9L.termsSum (colTerms tl mu c) x = 0) :=
        Prob.cnt_exists_mem_le _ _
    _ ≤ ∑ mu ∈ Finset.range tl.NM, (tl.mats.getD mu {}).k * (tl.tau - 1) := by
        refine Finset.sum_le_sum fun mu hmu => ?_
        refine (Prob.cnt_exists_mem_le _ _).trans ?_
        calc ∑ c ∈ Finset.range (tl.mats.getD mu {}).k,
              Prob.cnt (fun x : Cb.Gl.E => K9L.termsSum (colTerms tl mu c) x = 0)
            ≤ ∑ _c ∈ Finset.range (tl.mats.getD mu {}).k, (tl.tau - 1) :=
              Finset.sum_le_sum fun c hc =>
                K9L.count_terms Cb.Gl.E _ _ (colTerms_ok tl mu c)
                  (colTerms_live tl mu c (h mu (Finset.mem_range.1 hmu) c (Finset.mem_range.1 hc)))
          _ = (tl.mats.getD mu {}).k * (tl.tau - 1) := by simp
    _ = cols tl * (tl.tau - 1) := by
        unfold cols
        rw [Finset.sum_mul]

/-- **The count at the fall's own text.** -/
theorem k8Front_few (s : S) (tl : HTailF2) (hs : s.tl? = some tl) (h : allLive tl = true) :
    Prob.cnt (fun x : Cb.Gl.E => (k8Front s [chiAt x]).isSome = true) ≤ cols tl * (tl.tau - 1) := by
  refine (Prob.cnt_mono fun x hx => ?_).trans (front_few tl h)
  unfold k8Front at hx
  rw [hs] at hx
  simpa [chiAt] using hx

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.front_few
#print axioms ProofFile.Honest.K8.k8Front_few
#print axioms ProofFile.Honest.K8.allLive
#print axioms ProofFile.Honest.K8.cols
#print axioms ProofFile.Honest.K8.columnWeight_val
#print axioms ProofFile.Honest.K8.colTerms
#print axioms ProofFile.Honest.K8.colTerms_sum
#print axioms ProofFile.Honest.K8.colTerms_ok
#print axioms ProofFile.Honest.K8.colTerms_live
