-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EntriesFew.lean: A COUNT FOR A TEST THAT ASKS "NO WEIGHT ON THESE ENTRIES IS
0" OF VIRTUAL ROWS ON WHICH THE SMALLNESS TEST's TIES AND READS LAY NOTHING. A statement and its
proof. No prover. Lemmas; none of the library's goals.

  **`entries_few`**   batch, s, tl, F, g, nf, nb, a, d as in `FallFew`
      (Johnson/Desc/K8/Honest/FallCount.lean); t: an array; En: a finite set of its entries (virtual
      row, index), each in a row on which the ties and reads lay nothing (`OffAt`,
      Johnson/Desc/K8/Honest/WeightAt.lean); no: a test on the state behind. IF (hno) a yes of no,
      at a state behind that holds the data that the list "K8.equations" has returned at tl, names
      an entry of En whose weight in the ledger behind is 0; (hz0) each row of En begins at column 0
      in F, or its entry 0 is in En; (hlive) on each entry of En one of the first nf + 4 claims has
      a coefficient other than 0; and the plan's number of claims is at most d + 1: THEN at most
      |En| * d field elements are challenges at which batch says yes and, behind it, no says yes
The argument is that of `fall_few`: the weight of an entry is a polynomial in the challenge whose
coefficients stand outside the challenge; one of them is not 0; the library's count of roots. Where
a row's weights begin behind column 0 the ledger lays nothing on the row's entry 0: so the challenge
is a root of that entry's polynomial.
By: `behind_plain` (BehindTotal.lean) · `total_oneAt`, `total_below` (FallAlg.lean) ·
`plainTerms_ok`, `plainTerms_live` (WeightAt.lean) · K9L.count_terms.
Limits: `Gathers`, (hno), (hz0), (hlive) are premises.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.BehindTotal
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Tie.Pv.Tail.Port

/-- **The count.** -/
theorem entries_few (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (t : Nat)
    (En : Finset (ℕ × ℕ)) (no : S → Bool) (hoff : ∀ e ∈ En, OffAt tl t e.1)
    (hno : ∀ (t' : S) (tl' : HTailF2) (G : Fork), tlForkP.get? t' = some (tl', G) →
      (∃ (n₀ : Nat) (F₁ F₂ : Fork) (k8 : List Claim),
        equations n₀ tl funs F₁ = .ok (tl', F₂, k8)) → no t' = true →
      ∃ e ∈ En, (weightsOf G t e.1).getD e.2 zeroE = zeroE)
    (hz0 : ∀ e ∈ En, ((F.trees.getD t {}).rows.getD e.1 {}).L0 = 0 ∨ (e.1, 0) ∈ En)
    (hlive : ∀ e ∈ En, ∃ j, j < nf + 4 ∧ a j t e.1 e.2 ≠ 0)
    (hd : F.planClaimsF ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true) ≤ En.card * d := by
  have root : ∀ x : Cb.Gl.E, askBehind batch no s [chiAt x] = true →
      nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧
      ∃ e ∈ En, K9L.termsSum (plainTerms (fun j => a j t e.1 e.2) nf nb
        (tl.NM + (readsList tl funs).length)) x = 0 := by
    intro x hx
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      rw [hbt] at hx
      change no t' = true at hx
      obtain ⟨tl', G, g₀, h1, heq, -, shG, hcnt, -, hw⟩ :=
        behind_plain p g batch s t' tl F funs nf nb a hb hs hG x hbt
      refine ⟨hcnt, ?_⟩
      obtain ⟨e, he, hzero⟩ := hno t' tl' G h1 heq hx
      have hL : ((G.trees.getD t {}).rows.getD e.1 {}).L0 =
          ((F.trees.getD t {}).rows.getD e.1 {}).L0 := by
        rw [L0_of_shape, shG, ← L0_of_shape]
      by_cases h0 : ((F.trees.getD t {}).rows.getD e.1 {}).L0 = 0
      · refine ⟨e, he, ?_⟩
        rw [← hw t e.1 e.2 (hoff e he), total_oneAt Reading.gl G t _ _ (hL.trans h0), hzero]
        exact Reading.gl.zero
      · rcases hz0 e he with h | h
        · exact absurd h h0
        · refine ⟨(e.1, 0), h, ?_⟩
          rw [← hw t e.1 0 (hoff e he)]
          exact total_below Reading.gl G t _ 0 (by rw [hL]; exact Nat.pos_of_ne_zero h0)
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch no s [chiAt x] = true
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨hcnt, -⟩ := root x₀ hx₀
    calc Prob.cnt (fun x : Cb.Gl.E => askBehind batch no s [chiAt x] = true)
        ≤ Prob.cnt (fun x : Cb.Gl.E => ∃ e ∈ En,
            K9L.termsSum (plainTerms (fun j => a j t e.1 e.2) nf nb
              (tl.NM + (readsList tl funs).length)) x = 0) :=
          Prob.cnt_mono fun x hx => (root x hx).2
      _ ≤ ∑ e ∈ En, Prob.cnt (fun x : Cb.Gl.E =>
            K9L.termsSum (plainTerms (fun j => a j t e.1 e.2) nf nb
              (tl.NM + (readsList tl funs).length)) x = 0) :=
          Prob.cnt_exists_mem_le _ _
      _ ≤ ∑ _e ∈ En, d := by
          refine Finset.sum_le_sum fun e he => ?_
          obtain ⟨j, hj, ha⟩ := hlive e he
          exact K9L.count_terms Cb.Gl.E _ d
            (plainTerms_ok _ nf nb _ d (by omega)) (plainTerms_live _ nf nb _ j hj ha)
      _ = En.card * d := by simp
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.entries_few
