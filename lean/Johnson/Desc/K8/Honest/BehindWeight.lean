-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BehindWeight.lean: BEHIND A YES OF THE BATCHING BLOCK: EVERY WEIGHT THAT THE
LEDGER BEARS ON A COLUMN OF A VIRTUAL ROW, BY ITS VALUE, AS TERMS IN THE CHALLENGE. Lemmas; none of
the library's goals. No prover stands in them; nothing on completeness, soundness or hiding. An
assembly: no new argument.

  `weights_of_sums`, `weights_coefBody`   whatever keeps the ledger's sums (K9L.sums,
      Johnson/Desc/First/Batch/Law/Measure.lean) keeps every virtual row's weights on the columns;
      so the step that lays the rows' weights (coefBody)
  **`behind_weight`**   `behind_total` (Johnson/Desc/K8/Honest/BehindTotal.lean) where every virtual
      row of the ledger in front begins at column 0: the left side of its last clause is the value
      of the row's weight at the column
By: `total_oneAt` (Johnson/Desc/K8/Honest/FallAlg.lean) · `L0_of_shape` (FallDraw.lean) ·
K9L.core_coefBody (Johnson/Desc/First/Batch/Law/Coef.lean).
Limits. BY VALUES: no word of a weight is tied. `Gathers` and "begins at column 0" are premises. a,
the plain claims' coefficients, is a letter of `Gathers`: which of them are 0 on which rows is not
said; nor what the two differences of the ties' and reads' terms come to.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.BehindTotal
import Johnson.Desc.First.Batch.Law.Coef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- Whatever keeps the ledger's sums keeps every virtual row's weights on the columns. -/
theorem weights_of_sums {F G : Fork} (h : K9L.sums G = K9L.sums F) (t r : Nat) :
    weightsOf G t r = weightsOf F t r := by
  have e : ∀ H : Fork, weightsOf H t r = (((K9L.sums H).1.getD t #[]).getD r (#[], 0)).1 := by
    intro H
    simp only [weightsOf, K9L.sums, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases H.trees[t]? with
    | none => rfl
    | some X =>
      simp only [Option.map_some, Option.getD_some, Array.getElem?_map]
      cases X.rows[r]? <;> rfl
  rw [e G, e F, h]

/-- The step that lays the rows' weights leaves every virtual row's weights on the columns. -/
theorem weights_coefBody (tl : HTailF2) (g : Forest.Heard) (F : Fork) (t r : Nat) :
    weightsOf (coefBody tl g F) t r = weightsOf F t r :=
  weights_of_sums (congrArg (·.1) (K9L.core_coefBody tl g F)) t r

/-- **BEHIND A YES OF THE BATCHING BLOCK: EVERY WEIGHT ON A COLUMN, BY ITS VALUE, AS TERMS IN THE
CHALLENGE**: `behind_total` where every virtual row of the ledger in front begins at column 0. -/
theorem behind_weight (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s t' : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hG : Gathers p g s tl funs nf nb a) (x : Cb.Gl.E)
    (hbt : batch s [⟨[], chiAt x⟩] = .ok t')
    (hz : ∀ t r, ((F.trees.getD t {}).rows.getD r {}).L0 = 0) :
    ∃ (tl' : HTailF2) (G F₁ F₂ : Fork) (k8 : List Claim) (n₀ : Nat) (g₀ : Forest.Heard),
      tlForkP.get? t' = some (tl', G) ∧ equations n₀ tl funs F₁ = .ok (tl', F₂, k8) ∧
      tl.heard = some g₀ ∧ Reading.gl.val F₁.theta = x ∧ F₁.planClaimsF = F.planClaimsF ∧
      shapeOf F₁.trees = shapeOf F.trees ∧ shapeOf G.trees = shapeOf F.trees ∧
      nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧
      (∀ c cl, (K9L.four8 tl g₀)[c]? = some cl → ∀ t r i, a (nf + c) t r i = coefOn cl t r i) ∧
      ∀ t r i, ∃ tl1 : HTailF2, Powered tl1 F₁.theta ∧
        (∀ mu, mu < tl1.NM → tl1.gamV.getD mu #[] = gamAt tl1 mu) ∧
        tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid } ∧
        Reading.gl.val ((weightsOf G t r).getD i zeroE) =
          K9L.termsSum (fromOn (fun j => a j t r i) (nf + 4) 0) x +
          K9L.termsSum (fromOn (fun j => a j t r i) nb
            (nf + (4 + (tl.NM + (readsList tl funs).length)))) x +
          ((((List.range tl1.NM).map (tieTerm Reading.gl (oneAt t r i) tl1 F₁)).sum +
              sumFrom (readTerm Reading.gl (oneAt t r i) tl1 F₁) 0 (readsList tl1 funs)) -
            (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
              sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs))) := by
  obtain ⟨tl', G, F₁, F₂, k8, n₀, g₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, H⟩ :=
    behind_total p g batch s t' tl F funs nf nb a hb hs hG x hbt
  refine ⟨tl', G, F₁, F₂, k8, n₀, g₀, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun t r i => ?_⟩
  obtain ⟨tl1, hP, hgam, etl, hcut⟩ := H t r i
  refine ⟨tl1, hP, hgam, etl, ?_⟩
  rw [← total_oneAt Reading.gl G t r i (by rw [L0_of_shape, h7, ← L0_of_shape]; exact hz t r)]
  exact hcut

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.weights_of_sums
#print axioms VerifiableInference.Desc.First.K8.Honest.weights_coefBody
#print axioms VerifiableInference.Desc.First.K8.Honest.behind_weight
