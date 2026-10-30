-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TieWhole.lean: THE SMALLNESS TEST: THE TIE's HALF OF WHAT MUST NEVER FAIL IN
THE VERIFIER's TWO TESTS ON WEIGHTS BY A SECOND COMPUTATION (`TieEqs`, the second conjunct of
`SecondEqs`: Johnson/Desc/K8/Honest/SecondParts.lean), WHOLE, BEHIND THE ADDING: WHERE NO PLAIN
CLAIM BEARS ON THE TIES' ROW's DIGITS OR ON THE MATRICES' ARRAYS OF SYMBOLS. Lemmas; none of the
library's goals. On ledgers, lists of claims and plain data (`Added8`,
Johnson/Desc/K8/Honest/Added8.lean): no block, no prover; nothing on completeness, soundness or
hiding. An assembly.

  `laid_shape_apart`   what `symbolsLaid` (Johnson/Desc/K8/Honest/SymbolsFew.lean) gives of one
      matrix without naming a column: the shape's number of columns is the matrix's; the matrices'
      arrays of symbols differ
  **`Added8.tieEqs`**   all five parts of `TieEqs`, at the data behind and at the ledger behind the
      step that lays the rows' weights
By: `tie_lo`, `tie_coef`, `gam_word` (Johnson/Desc/K8/Honest/TieParts.lean) · `Added8.tie_digits`,
`Added8.tie_column`, `Added8.powered` (TieWords.lean) · `eq_gamX` (TiesAt.lean) · `k8_cut`
(FallReads.lean) · `weights_coefBody` (BehindWeight.lean) · `tiesLaid_spec` (LinkedFew.lean) ·
eq_same, at whole sentences that read planned fields alone
(Johnson/Desc/First/TailClaims/EquationsCover.lean) · K9L.core_coefBody
(Johnson/Desc/First/Batch/Law/Coef.lean).
Limits. EVERY PREMISE IS SHOWN OF NO STATE HERE: `Added8`; that the second computation's number of
blocks is the data's; `tiesLaid`, `symbolsLaid`, `TieFront`; "begins at column 0"; that each
matrix's array has a virtual row 0; `PlainOff` at the ties' row's digits and at the matrices'
arrays. Nothing on the pieces' half (`PieceEqs`).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.TieWords
import Johnson.Desc.K8.Honest.SecondParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- What `symbolsLaid` gives of one matrix without naming a column: the shape's number of columns
is the matrix's; the matrices' arrays of symbols differ. -/
theorem laid_shape_apart (tl : HTailF2) (h : symbolsLaid tl = true) (mu : Nat) (hmu : mu < tl.NM) :
    (tl.shp.getD mu {}).k = (tl.mats.getD mu {}).k ∧
      ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b := by
  simp only [symbolsLaid, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range] at h
  refine ⟨(h mu hmu).1.2, fun a ha b hb e => ?_⟩
  rcases (h b hb).2 a ha with k | k
  · exact k
  · exact absurd e k

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **THE TIE's HALF OF WHAT MUST NEVER FAIL, WHOLE, BEHIND THE ADDING**: all five parts of
`TieEqs`, at the data behind and the ledger behind the step that lays the rows' weights: where no
plain claim bears on the ties' row's digits or on the matrices' arrays of symbols. -/
theorem Added8.tieEqs (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (nbW : Nat) (hn : nbW = tl.zzBlocks) (hL : tiesLaid tl = true) (hS : symbolsLaid tl = true)
    (hF : TieFront tl) (hz : ∀ t r, ((Y.trees.getD t {}).rows.getD r {}).L0 = 0)
    (hrow : ∀ mu, mu < tl.NM → HasRow G (tl.gtTree.getD mu 0) 0)
    (hoffT : ∀ mu, mu < tl.NM → ∀ i, i < (tl.mats.getD mu {}).m → ∀ plane, plane ≤ 1 →
      PlainOff fr k8 bk tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i))
    (hoffS : ∀ mu, mu < tl.NM → ∀ c, c < (tl.mats.getD mu {}).k →
      PlainOff fr k8 bk (tl.gtTree.getD mu 0) 0 c)
    (mu : Nat) (hmu : mu < tl.NM) :
    TieEqs tl' (coefBody tl' g G) (tiesL tl' (coefBody tl' g G) nbW) mu := by
  obtain ⟨cθ, cp, -, -⟩ := A.core
  have hP := A.powered
  have bθ : (coefBody tl' g G).theta = Y.theta :=
    (congrArg (·.2.1) (K9L.core_coefBody tl' g G)).trans cθ
  have bp : (coefBody tl' g G).planClaimsF = Y.planClaimsF :=
    (congrArg (·.2.2.2) (K9L.core_coefBody tl' g G)).trans cp
  have eN : tl'.NM = tl.NM :=
    eq_same (·.NM) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eL : tiesLaid tl' = tiesLaid tl := eq_same (fun t : HTailF2 => tiesLaid t) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eS : symbolsLaid tl' = symbolsLaid tl := eq_same (fun t : HTailF2 => symbolsLaid t) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eτ : tl'.tau = tl.tau :=
    eq_same (·.tau) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eg : tl'.gtTree = tl.gtTree :=
    eq_same (·.gtTree) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eb : tl'.zzBlocks = tl.zzBlocks :=
    eq_same (·.zzBlocks) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have hmu' : mu < tl'.NM := by rw [eN]; exact hmu
  have L' := tiesLaid_spec tl' (eL.trans hL)
  have hS' : symbolsLaid tl' = true := eS.trans hS
  have hsh := hP.shape mu hmu'
  -- the two sentences on words, in the letters of the data behind
  have dig : ∀ i, i < (tl'.mats.getD mu {}).m →
      (weightsOf G tl'.ix.ZZ tl'.zzRowTies).getD (tl'.off.getD mu 0 + i) zeroE =
          tieV (powE Y.theta (Y.planClaimsF + tl'.firstAgain mu))
            ((powersAgain Y.theta (pow2Again tl'.tau) (tl'.shp.getD mu {}).mS).getD (i / 3)
              zeroE) i ∧
        (weightsOf G tl'.ix.ZZ tl'.zzRowTies).getD (tl'.mz + tl'.off.getD mu 0 + i) zeroE =
          scaleNat (tieV (powE Y.theta (Y.planClaimsF + tl'.firstAgain mu))
            ((powersAgain Y.theta (pow2Again tl'.tau) (tl'.shp.getD mu {}).mS).getD (i / 3)
              zeroE) i) (2 ^ t2D0) :=
    (eq_same (fun t : HTailF2 => ∀ i, i < (t.mats.getD mu {}).m →
      (weightsOf G t.ix.ZZ t.zzRowTies).getD (t.off.getD mu 0 + i) zeroE =
          tieV (powE Y.theta (Y.planClaimsF + t.firstAgain mu))
            ((powersAgain Y.theta (pow2Again t.tau) (t.shp.getD mu {}).mS).getD (i / 3)
              zeroE) i ∧
        (weightsOf G t.ix.ZZ t.zzRowTies).getD (t.mz + t.off.getD mu 0 + i) zeroE =
          scaleNat (tieV (powE Y.theta (Y.planClaimsF + t.firstAgain mu))
            ((powersAgain Y.theta (pow2Again t.tau) (t.shp.getD mu {}).mS).getD (i / 3)
              zeroE) i) (2 ^ t2D0)) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)).mpr
      fun i hi => A.tie_digits hL hF mu i hmu hi (hz _ _) (hoffT mu hmu i hi)
  have col : ∀ c, c < (tl'.mats.getD mu {}).k →
      (weightsOf G (tl'.gtTree.getD mu 0) 0).getD c zeroE =
        mulE (subE zeroE (powE Y.theta (Y.planClaimsF + tl'.firstAgain mu)))
          (sumAgain tl'.cfF
            (((List.range mu).foldl (fun n nu => n + (tl'.mats.getD nu {}).k) 0 + c) * tl'.tau)
            ((Array.range tl'.tau).map fun u => powE Y.theta u) tl'.tau 0 zeroE) :=
    (eq_same (fun t : HTailF2 => ∀ c, c < (t.mats.getD mu {}).k →
      (weightsOf G (t.gtTree.getD mu 0) 0).getD c zeroE =
        mulE (subE zeroE (powE Y.theta (Y.planClaimsF + t.firstAgain mu)))
          (sumAgain t.cfF
            (((List.range mu).foldl (fun n nu => n + (t.mats.getD nu {}).k) 0 + c) * t.tau)
            ((Array.range t.tau).map fun u => powE Y.theta u) t.tau 0 zeroE)) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)).mpr
      fun c hc => A.tie_column hF mu c (symAt_of_laid tl hS mu c hmu hc) (hz _ _)
        (hoffS mu hmu c hc)
  have tri : ∀ j, tl'.cfF.getD j 0 = 1 ∨ tl'.cfF.getD j 0 = -1 ∨ tl'.cfF.getD j 0 = 0 :=
    (eq_same (fun t : HTailF2 => ∀ j, t.cfF.getD j 0 = 1 ∨ t.cfF.getD j 0 = -1 ∨
      t.cfF.getD j 0 = 0) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)).mpr hF.trits
  have fst : tl'.cfFirst.getD mu 0 =
      (List.range mu).foldl (fun n nu => n + (tl'.mats.getD nu {}).k) 0 :=
    (eq_same (fun t : HTailF2 => t.cfFirst.getD mu 0 =
      (List.range mu).foldl (fun n nu => n + (t.mats.getD nu {}).k) 0) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)).mpr (hF.first mu hmu)
  have eT : tiesL tl' (coefBody tl' g G) nbW = weightsOf G tl'.ix.ZZ tl'.zzRowTies := by
    have e1 : 2 * nbW + 1 = tl'.zzRowTies := by
      unfold HTailF2.zzRowTies
      rw [eb, hn]
    unfold tiesL
    rw [e1]
    exact weights_coefBody tl' g G _ _
  have eC : (((coefBody tl' g G).trees.getD (tl'.gtTree.getD mu 0) {}).rows.getD 0 {}).L =
      weightsOf G (tl'.gtTree.getD mu 0) 0 := weights_coefBody tl' g G _ _
  have hk : (tl'.shp.getD mu {}).k = (tl'.mats.getD mu {}).k :=
    (laid_shape_apart tl' hS' mu hmu').1
  obtain ⟨tl1, -, hgam, etl, -⟩ := k8_cut A.eq
  have gV : tl'.gamV.getD mu #[] = gamAt tl' mu := by
    have e1 : tl'.gamV = tl1.gamV := (congrArg (fun z : HTailF2 => z.gamV) etl).trans rfl
    have e2 : gamAt tl' mu = gamAt tl1 mu :=
      (congrArg (fun z : HTailF2 => gamAt z mu) etl).trans rfl
    have e3 : tl'.NM = tl1.NM := (congrArg (fun z : HTailF2 => z.NM) etl).trans rfl
    rw [e1, e2]
    exact hgam mu (e3 ▸ hmu')
  unfold TieEqs
  dsimp only
  rw [bθ, bp, eT, eC]
  refine ⟨tie_lo hP hmu', fun R hR => ?_, ?_, fun R hR i h1 h2 => ?_, fun c hc => ?_⟩
  · have k := tie_coef tl' g G (by rw [cθ]; exact hP) hmu'
      (by rw [eg]; exact hrow mu hmu) (laid_shape_apart tl' hS' mu hmu').2
      (by rw [eτ]; exact hF.tau)
      (hsh.2.2.1 ▸ hR)
    rw [cθ] at k
    exact k
  · have h5 := hsh.2.2.2.2
    have h6 := L'.fit mu hmu'
    omega
  · have h6 := L'.fit mu hmu'
    have hi : i < (tl'.mats.getD mu {}).m := by omega
    have hq : i / 3 = R := by omega
    obtain ⟨a, b⟩ := dig i hi
    rw [hq] at a b
    exact ⟨a, b⟩
  · have hc' : c < (tl'.mats.getD mu {}).k := hk ▸ hc
    refine ⟨?_, ?_, col c hc'⟩
    · rw [eq_gamX A.eq mu hmu']
      exact gam_word hP mu c hc' tri fst
    · rw [gV]
      exact gam_word hP mu c hc' tri fst

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.laid_shape_apart
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.tieEqs
