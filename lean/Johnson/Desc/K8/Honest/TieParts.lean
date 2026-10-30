-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/TieParts.lean: THE SMALLNESS TEST: THE PARTS OF THE VERIFIER's TEST ON A
TIE's WEIGHTS BY A SECOND COMPUTATION (tieWeightsHeld, OnBytes/Model/Tail.lean; `TieEqs`,
Johnson/Desc/K8/Honest/SecondParts.lean) THAT READ NO WEIGHT ON A COLUMN: EACH EQUALITY AS AN
EQUALITY OF WORDS. A definition and lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding.

  `tie_lo`   where the data hold the batching element's powers: the first of the weights inside a
      row of the array is 1
  **`tie_coef`**   the weights on the rows of a matrix's array, behind the step that lays them, are
      the second computation's powers
  `tieV ka hiR i`, `tieV_ok`, `radb_two`, `tieV_val`   the value that the test expects on the low
      digit of row i of cells; it is a word below the prime; the radix reads as 2^20 (the step
      inside `radb_val`'s proof, Johnson/Desc/K8/Honest/SecondNz.lean, written a second time); the
      expected value, read
  `foldColumn_ok`, **`gam_word`**   the first computation's sum over a column is a word below the
      prime; it IS the second computation's, WHERE THE DRAWN MATRIX's ENTRIES ARE 1, -1 OR 0 AND THE
      MATRIX's FIRST COLUMN IS THE SUM OF THE NUMBERS OF COLUMNS IN FRONT
By: `coef_mat`, `rowX_powers` (Johnson/Desc/K8/Honest/CoefClosed.lean) · `powers_eq_powE`
(RestPowers.lean) · `powersAgain_ok`, `sumAgain_ok`, `sumAgain_col`, `okE_scale` (AgainVals.lean) ·
ProdV.gl_inj (Johnson/Desc/First/ProdV/Drawn.lean) · K3.okE_pow
(Johnson/Top/H/K3Via/BridgeProof.lean) · powersAgain_val, pow2Again_tau
(OnBytes/Tie/Pv/Tail/EndTested.lean) · gamAt_val (EndLoopsB.lean) · val_two_pow (EndClaims.lean) ·
scaleE_val (OnBytes/Iop/RowLaws.lean).
Limits. `Powered`, the premises on the ledger's frame, the bound on tau and the two premises of
`gam_word` are shown of no state here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.AgainVals
import Johnson.Desc.K8.Honest.RestPowers
import OnBytes.Tie.Pv.Tail.EndClosed
import OnBytes.Tie.Pv.Tail.EndClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered getD_map getD_map_range powersAgain_val pow2Again_tau
  val_two_pow gamAt gamAt_val signOf)
open VerifiableInference.Desc.First.TailClaims (coefBody)

/-- T1: the first of the weights inside a row of the array is 1. -/
theorem tie_lo {tl : HTailF2} {theta : E} (hP : Powered tl theta) {mu : Nat} (hmu : mu < tl.NM) :
    (tl.loX.getD mu #[]).getD 0 zeroE = oneE := by
  rw [hP.loX, getD_map _ _ _ _ {} (hP.lt_shp mu hmu)]
  rfl

/-- T2's equality: the weights on the rows of a matrix's array, behind the step that lays them, are
the second computation's powers, as words. -/
theorem tie_coef (tl : HTailF2) (g : Forest.Heard) (F : Fork) (hP : Powered tl F.theta) {mu : Nat}
    (hmu : mu < tl.NM) (hr : HasRow F (tl.gtTree.getD mu 0) 0)
    (hinj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b)
    (hτ : tl.tau ≤ 2 ^ 64) {R : Nat} (hR : R < (tl.shp.getD mu {}).mS) :
    (((coefBody tl g F).trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).coef.getD R zeroE =
      (powersAgain F.theta (pow2Again tl.tau) (tl.shp.getD mu {}).mS).getD R zeroE := by
  have e : (((coefBody tl g F).trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}).coef =
      tl.rowX.getD mu #[] := coef_mat tl g F hmu hr hinj
  rw [e, rowX_powers hP (hP.lt_shp mu hmu), powers_eq_powE _ _ _ hR]
  refine ProdV.gl_inj _ _ (K3.okE_pow _ _) (powersAgain_ok _ _ _ _ hR) ?_
  rw [powersAgain_val Reading.gl _ _ _ _ hR, Reading.gl.pow, Reading.gl.pow, pow2Again_tau tl hτ,
    ← pow_mul]

/-- The value that the tie's test expects on the low digit of row i of cells. -/
def tieV (ka hiR : E) (i : Nat) : E :=
  if i % 3 = 0 then mulE ka hiR
  else if i % 3 = 1 then scaleE (fOfNat radb) (mulE ka hiR)
  else scaleE (fOfNat radb) (scaleE (fOfNat radb) (mulE ka hiR))

theorem tieV_ok (ka hiR : E) (i : Nat) : OnBytes.okE (tieV ka hiR i) = true := by
  unfold tieV
  split_ifs
  · exact Part.MaskedSum.okE_mul _ _
  · exact okE_scale _ _
  · exact okE_scale _ _

/-- The radix reads as 2^20: the step inside `radb_val`'s proof (SecondNz.lean), stated. -/
theorem radb_two : Reading.gl.val (ofF (fOfNat radb)) = (2 : Cb.Gl.E) ^ 20 :=
  val_two_pow Reading.gl 20 (by decide +kernel)

theorem tieV_val (ka hiR : E) (i : Nat) :
    Reading.gl.val (tieV ka hiR i) =
      ((2 : Cb.Gl.E) ^ 20) ^ (i % 3) * (Reading.gl.val ka * Reading.gl.val hiR) := by
  have h3 : i % 3 < 3 := Nat.mod_lt _ (by decide)
  unfold tieV
  split_ifs with h0 h1
  · rw [h0, pow_zero, one_mul, Reading.gl.mul]
  · rw [h1, pow_one, OnBytes.scaleE_val, radb_two, Reading.gl.mul]
  · have h2 : i % 3 = 2 := by omega
    rw [h2, OnBytes.scaleE_val, OnBytes.scaleE_val, radb_two, Reading.gl.mul]
    ring

/-- The first computation's sum over a column is a word below the prime. -/
theorem foldColumn_ok (cf : Array Int) (base tau : Nat) (v : Array E) :
    OnBytes.okE (foldColumn cf base tau v) = true := by
  have key : ∀ (l : List E) (s : E × Nat), OnBytes.okE s.1 = true →
      OnBytes.okE (l.foldl (fun (s : E × Nat) y =>
        let x := cf.getD (base + s.2) 0
        (if x == 0 then s.1 else if x < 0 then subE s.1 y else addE s.1 y, s.2 + 1)) s).1 =
        true := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons y l ih =>
      intro s h
      rw [List.foldl_cons]
      refine ih _ ?_
      dsimp only
      split
      · exact h
      · split
        · exact Part.MaskedSum.okE_sub _ _
        · exact Part.MaskedSum.okE_add _ _
  unfold HTailF2.foldColumn
  rw [← Array.foldl_toList]
  exact key _ _ rfl

/-- T6's first two: a column's sum by the first computation is the second computation's, as
words: where the drawn matrix's entries are 1, -1 or 0 and the matrix's first column is the sum of
the numbers of columns in front. -/
theorem gam_word {tl : HTailF2} {theta : E} (hP : Powered tl theta) (mu c : Nat)
    (hc : c < (tl.mats.getD mu {}).k)
    (hT : ∀ j, tl.cfF.getD j 0 = 1 ∨ tl.cfF.getD j 0 = -1 ∨ tl.cfF.getD j 0 = 0)
    (hcf : tl.cfFirst.getD mu 0 =
      (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0) :
    (gamAt tl mu).getD c zeroE =
      sumAgain tl.cfF (((List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0 + c) *
        tl.tau) ((Array.range tl.tau).map fun u => powE theta u) tl.tau 0 zeroE := by
  refine ProdV.gl_inj _ _ ?_ (sumAgain_ok _ _ _ _ _ _ rfl) ?_
  · unfold gamAt
    rw [getD_map_range _ _ _ _ hc]
    exact foldColumn_ok _ _ _ _
  · rw [gamAt_val Reading.gl hP mu c hc, sumAgain_col _ _ _ _ fun u => hT _, hcf]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [getD_map_range _ _ _ _ (Finset.mem_range.1 hu), Reading.gl.pow]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tie_lo
#print axioms VerifiableInference.Desc.First.K8.Honest.tie_coef
#print axioms VerifiableInference.Desc.First.K8.Honest.tieV_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.radb_two
#print axioms VerifiableInference.Desc.First.K8.Honest.tieV_val
#print axioms VerifiableInference.Desc.First.K8.Honest.foldColumn_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.gam_word
