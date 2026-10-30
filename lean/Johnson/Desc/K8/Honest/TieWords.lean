-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TieWords.lean: THE SMALLNESS TEST: BEHIND THE ADDING, THE TWO DIGITS OF A ROW
OF CELLS IN THE TIES' ROW OF THE DIGITS' ARRAY, AND A COLUMN OF A MATRIX's ARRAY OF SYMBOLS, BEAR
JUST THE WORDS THAT THE VERIFIER's SECOND COMPUTATION EXPECTS (the fourth part, and the last clause
of the fifth, of `TieEqs`, Johnson/Desc/K8/Honest/SecondParts.lean): WHERE NO PLAIN CLAIM BEARS ON
THE ENTRY. A definition and lemmas; none of the library's goals. On ledgers, lists of claims and
plain data (`Added8`, Johnson/Desc/K8/Honest/Added8.lean): no block, no prover; nothing on
completeness, soundness or hiding.

  `TieFront tl`   on public numbers and on the drawn matrix, in front of the batching: tau and each
      (m + 2) / 3 are at most 2^64; the drawn matrix's entries are 1, -1 or 0; each matrix's first
      column is the sum of the numbers of columns in front
  `Added8.powered`, `Added8.mS`, `Added8.first`   the data behind hold the powers of the batching
      element; the shapes' numbers of rows of symbols; the second computation's index of a matrix's
      first equation is the first's
  **`Added8.tie_digits`**, **`Added8.tie_column`**   the sentences of the title, as equalities of
      words, in the letters of the data in front and of the ledger in front of the adding
By: `Added8.weight_tie`, `Added8.weight_sym`, `Added8.core` (Added8.lean) · `tieV_val`, `tieV_ok`
(TieParts.lean) · `sumAgain_col`, `firstAgain_eq`, `okE_scaleNat` (AgainVals.lean) · `word_of_val`
(OkWeights.lean) · `powered_of_yes` (PoweredOfYes.lean) · eq_same
(Johnson/Desc/First/TailClaims/EquationsCover.lean) · powersAgain_val, pow2Again_tau
(OnBytes/Tie/Pv/Tail/EndTested.lean) · Fo.scaleNat_val (OnBytes/Tie/Pv/Lookup/Ends/FoNatVal.lean).
Limits. `Added8`, `PlainOff`, `TieFront`, `tiesLaid`, `SymAt` and "begins at column 0" are premises.
`TieEqs` is not assembled here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.Added8
import Johnson.Desc.K8.Honest.TieParts
import Johnson.Desc.K8.Honest.PoweredOfYes
import OnBytes.Tie.Pv.Lookup.Ends.FoNatVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- **On public numbers and on the drawn matrix, in front of the batching**: what the tie's half
asks beside `tiesLaid` and `symbolsLaid`: two bounds; the drawn matrix's entries are 1, -1 or 0;
each matrix's first column is the sum of the numbers of columns in front. -/
structure TieFront (tl : HTailF2) : Prop where
  tau : tl.tau ≤ 2 ^ 64
  rows : ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64
  trits : ∀ j, tl.cfF.getD j 0 = 1 ∨ tl.cfF.getD j 0 = -1 ∨ tl.cfF.getD j 0 = 0
  first : ∀ mu, mu < tl.NM → tl.cfFirst.getD mu 0 =
    (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- The data behind hold the powers of Y's batching element. -/
theorem Added8.powered (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) : Powered tl' Y.theta := by
  have h := powered_of_yes A.eq
  rwa [A.th] at h

/-- The shapes' numbers of rows of symbols, in the letters of the data in front. -/
theorem Added8.mS (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (mu : Nat) (hmu : mu < tl.NM) :
    (tl.shp.getD mu {}).R = (tl.shp.getD mu {}).mS ∧
      (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3 := by
  have e : (mu < tl'.NM → (tl'.shp.getD mu {}).R = (tl'.shp.getD mu {}).mS ∧
      (tl'.shp.getD mu {}).mS = ((tl'.mats.getD mu {}).m + 2) / 3) =
      (mu < tl.NM → (tl.shp.getD mu {}).R = (tl.shp.getD mu {}).mS ∧
      (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3) :=
    eq_same (fun t : HTailF2 => mu < t.NM → (t.shp.getD mu {}).R = (t.shp.getD mu {}).mS ∧
      (t.shp.getD mu {}).mS = ((t.mats.getD mu {}).m + 2) / 3) A.eq
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  exact e.mp (fun h => ⟨(A.powered.shape mu h).2.2.1, (A.powered.shape mu h).2.2.2.2⟩) hmu

/-- The second computation's index of a matrix's first equation is the first's. -/
theorem Added8.first (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (hF : TieFront tl) (mu : Nat)
    (hmu : mu < tl.NM) : tl.firstAgain mu = firstOf tl mu :=
  firstAgain_eq tl hF.tau mu fun nu hnu =>
    ⟨hF.rows nu (by omega), (A.mS nu (by omega)).2⟩

/-- **T5, AS WORDS, in the letters of the data in front**: the two digits of row i of cells of
matrix mu in the ties' row bear just what the second computation expects. -/
theorem Added8.tie_digits (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀)
    (hL : tiesLaid tl = true) (hF : TieFront tl) (mu i : Nat) (hmu : mu < tl.NM)
    (hi : i < (tl.mats.getD mu {}).m)
    (h0 : ((Y.trees.getD tl.ix.ZZ {}).rows.getD tl.zzRowTies {}).L0 = 0)
    (hoff : ∀ plane, plane ≤ 1 →
      PlainOff fr k8 bk tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)) :
    (weightsOf G tl.ix.ZZ tl.zzRowTies).getD (tl.off.getD mu 0 + i) zeroE =
        tieV (powE Y.theta (Y.planClaimsF + tl.firstAgain mu))
          ((powersAgain Y.theta (pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD (i / 3) zeroE) i ∧
      (weightsOf G tl.ix.ZZ tl.zzRowTies).getD (tl.mz + tl.off.getD mu 0 + i) zeroE =
        scaleNat (tieV (powE Y.theta (Y.planClaimsF + tl.firstAgain mu))
          ((powersAgain Y.theta (pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD (i / 3) zeroE) i)
          (2 ^ t2D0) := by
  have hR : i / 3 < (tl.shp.getD mu {}).mS := by
    rw [(A.mS mu hmu).2]
    omega
  have hv : Reading.gl.val (tieV (powE Y.theta (Y.planClaimsF + tl.firstAgain mu))
      ((powersAgain Y.theta (pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD (i / 3) zeroE) i) =
      Reading.gl.val Y.theta ^ (Y.planClaimsF + firstOf tl mu + tl.stepF * (i / 3)) *
        ((2 : Cb.Gl.E) ^ 20) ^ (i % 3) := by
    rw [tieV_val, Reading.gl.pow, powersAgain_val Reading.gl _ _ _ _ hR, A.first hF mu hmu,
      pow2Again_tau tl hF.tau, pow_add (Reading.gl.val Y.theta) (Y.planClaimsF + firstOf tl mu)]
    ring
  have w0 := A.weight_tie hL mu 0 i hmu (by omega) hi h0 (hoff 0 (by omega))
  have w1 := A.weight_tie hL mu 1 i hmu (by omega) hi h0 (hoff 1 (by omega))
  rw [Nat.zero_mul, Nat.zero_add] at w0
  rw [Nat.one_mul] at w1
  refine ⟨word_of_val A.core.2.2.2 (tieV_ok _ _ _) ?_,
    word_of_val A.core.2.2.2 (okE_scaleNat _ _) ?_⟩
  · rw [w0, hv, pow_zero, one_mul]
  · rw [w1, Fo.scaleNat_val Reading.gl, hv, pow_one]
    have e : ((2 ^ t2D0 : ℕ) : Cb.Gl.E) = (2 : Cb.Gl.E) ^ 10 := by
      show ((2 ^ 10 : ℕ) : Cb.Gl.E) = _
      push_cast
      rfl
    rw [e]
    ring

/-- **T6's THIRD, AS WORDS, in the letters of the data in front**: column c of matrix mu's array of
symbols bears just what the second computation expects. -/
theorem Added8.tie_column (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (hF : TieFront tl)
    (mu c : Nat) (h : SymAt tl mu c)
    (h0 : ((Y.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).L0 = 0)
    (hoff : PlainOff fr k8 bk (tl.gtTree.getD mu 0) 0 c) :
    (weightsOf G (tl.gtTree.getD mu 0) 0).getD c zeroE =
      mulE (subE zeroE (powE Y.theta (Y.planClaimsF + tl.firstAgain mu)))
        (sumAgain tl.cfF
          (((List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0 + c) * tl.tau)
          ((Array.range tl.tau).map fun u => powE Y.theta u) tl.tau 0 zeroE) := by
  refine word_of_val A.core.2.2.2 (Part.MaskedSum.okE_mul _ _) ?_
  rw [A.weight_sym mu c h h0 hoff, Reading.gl.mul, Reading.gl.sub, Reading.gl.zero,
    Reading.gl.pow, A.first hF mu h.1, sumAgain_col _ _ _ _ fun u => hF.trits _,
    hF.first mu h.1]
  have e : ∀ u ∈ Finset.range tl.tau,
      signOf (K := Cb.Gl.E) (tl.cfF.getD
        (((List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0 + c) * tl.tau + u) 0) *
        Reading.gl.val (((Array.range tl.tau).map fun u => powE Y.theta u).getD u zeroE) =
      signOf (K := Cb.Gl.E) (tl.cfF.getD
        (((List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0 + c) * tl.tau + u) 0) *
        Reading.gl.val Y.theta ^ u := fun u hu => by
    rw [getD_map_range _ _ _ _ (Finset.mem_range.1 hu), Reading.gl.pow]
  rw [Finset.sum_congr rfl e]
  ring

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.powered
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.mS
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.first
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.tie_digits
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.tie_column
