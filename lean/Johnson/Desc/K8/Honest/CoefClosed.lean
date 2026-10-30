-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/CoefClosed.lean: THE SMALLNESS TEST: THE ROW WEIGHTS THAT THE VERIFIER's
ROUTINE coefficientsF (OnBytes/Model/Tail.lean) LAYS ON THE FIRST VIRTUAL ROW OF A MATRIX's ARRAY OF
SYMBOLS AND ON THE TWO LAST VIRTUAL ROWS OF THE DIGITS' ARRAY, IN CLOSED FORM. Statements and
proofs. On plain data: a record, what the lookup has heard, a ledger: no block, no prover. Lemmas;
none of the library's goals.

tl: the smallness test's data. g: what the digits' lookup has heard. F: a ledger. `coefAll tl g F`:
the ledger behind the routine, `rowAt`, `HasRow` (OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean).
  `formPowers_coef`   laying a product form leaves the written weights
  **`coef_mat`**   where no two matrices have one array: the weights of virtual row 0 of matrix mu's
      array are tl.rowX[mu]
  **`coef_powers`**   the weights of the digits' array's rows for the reads and for the ties are
      tl.vt and tl.vp
  **`rowX_powers`**, `rowX_size`, `rowX_val`   under `Powered tl theta`
      (OnBytes/Tie/Pv/Tail/EndClosed.lean): tl.rowX[mu] is the list of the first mS powers of theta
      ^ stepF; its length; what its entries read as
  **`differ_no_powers`**   so where the test "no two neighbours of the sorted list are equal" says
      no of that row's weights, two of these powers are equal: the event that `powers_meet_few`
      (Johnson/Desc/K8/Honest/PowersMeet.lean) counts
By: Fo.foldl_last, coefMats_eq, rowAt_mats, rowAt_onRow_eq, rowAt_onRow_ne and the frames' lemmas
(FoCoef.lean) · powers_val, powers_size (OnBytes/Tie/Pv/Tail/EndClaimsB.lean) · Reading.pow
(OnBytes/Model/HideLaws.lean) · `powers_of_no` (Johnson/Desc/K8/Honest/SortedDiffer.lean).
Limits. `HasRow`, "no two matrices one array", `Powered` are premises here. Nothing on the weights
on the columns (the field L). Nothing on the product forms beside the written weights. No count.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef
import OnBytes.Tie.Pv.Tail.EndClosed
import Johnson.Desc.K8.Honest.SortedDiffer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (coefAll coefMats coefBZ coefPowers rowAt HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered powers_val powers_size)

/-- Laying a product form leaves the written weights. -/
theorem formPowers_coef (row : HRow) (base : E) (rows : Nat) :
    (formPowers row base rows).coef = row.coef := rfl

/-- **The weights of a matrix's array's first virtual row.** -/
theorem coef_mat (tl : HTailF2) (g : Forest.Heard) (F : Fork) {mu : Nat} (hmu : mu < tl.NM)
    (hr : HasRow F (tl.gtTree.getD mu 0) 0)
    (hinj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b) :
    (rowAt (coefAll tl g F) (tl.gtTree.getD mu 0) 0).coef = tl.rowX.getD mu #[] := by
  have fr := (((Fo.frame_tables tl F).trans (Fo.frame_pieces tl g _)).trans
    (Fo.frame_powers tl F.theta _)).trans (Fo.frame_bz tl g _)
  have hn : ((List.range tl.NM).map fun a => (tl.gtTree.getD a 0, 0)).Nodup := by
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    exact hinj a (List.mem_range.1 ha) b (List.mem_range.1 hb) (congrArg Prod.fst e)
  unfold coefAll
  rw [Fo.coefMats_eq]
  exact Fo.foldl_last (fun a => tl.gtTree.getD a 0) (fun _ => 0)
    (fun _ a row => formPowers { row with coef := tl.rowX.getD a #[] } (powE F.theta tl.stepF)
      (tl.shp.getD a {}).mS)
    (fun a => tl.rowX.getD a #[]) (fun _ => True) (fun _ _ _ => trivial) (fun _ _ _ _ => rfl)
    (List.range tl.NM) _ trivial hn mu (List.mem_range.2 hmu) (fr.hasRow hr)

/-- **The weights of the digits' array's two last virtual rows.** -/
theorem coef_powers (tl : HTailF2) (g : Forest.Heard) (F : Fork)
    (hR : HasRow F tl.ix.ZZ tl.zzRowReads) (hT : HasRow F tl.ix.ZZ tl.zzRowTies)
    (hB : tl.ix.BZ ≠ tl.ix.ZZ) (hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ) :
    (rowAt (coefAll tl g F) tl.ix.ZZ tl.zzRowReads).coef = tl.vt ∧
      (rowAt (coefAll tl g F) tl.ix.ZZ tl.zzRowTies).coef = tl.vp := by
  have fr := (Fo.frame_tables tl F).trans (Fo.frame_pieces tl g _)
  have hne : ¬ (tl.ix.ZZ = tl.ix.ZZ ∧ tl.zzRowTies = tl.zzRowReads) := by
    unfold HTailF2.zzRowTies HTailF2.zzRowReads
    omega
  unfold coefAll
  refine ⟨?_, ?_⟩
  · rw [Fo.rowAt_mats _ _ _ _ _ fun mu hmu hh => hm mu hmu hh.1]
    unfold coefBZ
    rw [Fo.rowAt_onRow_ne _ _ (fun h => hB h.1), Fo.rowAt_onRow_ne _ _ (fun h => hB h.1),
      Fo.rowAt_onRow_ne _ _ (fun h => hB h.1)]
    unfold coefPowers
    rw [Fo.rowAt_onRow_ne _ _ hne, Fo.rowAt_onRow_eq _ _ (fr.hasRow hR)]
    rfl
  · rw [Fo.rowAt_mats _ _ _ _ _ fun mu hmu hh => hm mu hmu hh.1]
    unfold coefBZ
    rw [Fo.rowAt_onRow_ne _ _ (fun h => hB h.1), Fo.rowAt_onRow_ne _ _ (fun h => hB h.1),
      Fo.rowAt_onRow_ne _ _ (fun h => hB h.1)]
    unfold coefPowers
    rw [Fo.rowAt_onRow_eq _ _ ((fr.trans (Fo.frame_onRow _ _ _ _)).hasRow hT)]
    rfl

/-- **The list of weights is a list of powers.** -/
theorem rowX_powers {tl : HTailF2} {theta : E} (hP : Powered tl theta) {mu : Nat}
    (hmu : mu < tl.shp.size) :
    tl.rowX.getD mu #[] = powers (powE theta tl.stepF) (tl.shp.getD mu {}).mS := by
  rw [hP.rowX]
  simp [Array.getD, hmu]

theorem rowX_size {tl : HTailF2} {theta : E} (hP : Powered tl theta) {mu : Nat}
    (hmu : mu < tl.shp.size) : (tl.rowX.getD mu #[]).size = (tl.shp.getD mu {}).mS := by
  rw [rowX_powers hP hmu, powers_size]

theorem rowX_val {tl : HTailF2} {theta : E} (hP : Powered tl theta) {mu : Nat}
    (hmu : mu < tl.shp.size) {R : Nat} (hR : R < (tl.shp.getD mu {}).mS) :
    Reading.gl.val ((tl.rowX.getD mu #[]).getD R zeroE) =
      (Reading.gl.val theta ^ tl.stepF) ^ R := by
  rw [rowX_powers hP hmu, powers_val Reading.gl _ _ _ hR, Reading.pow]

/-- An array's entry, read off its list. -/
theorem toList_getD (a : Array E) (R : Nat) : a.toList.getD R zeroE = a.getD R zeroE := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- **A no of the test on the row's sorted weights: two of the powers are equal.** -/
theorem differ_no_powers (tl : HTailF2) (g : Forest.Heard) (F : Fork) (theta : E)
    (le : E → E → Bool) {mu : Nat} (hmu : mu < tl.NM) (hs : mu < tl.shp.size)
    (hr : HasRow F (tl.gtTree.getD mu 0) 0)
    (hinj : ∀ a, a < tl.NM → ∀ b, b < tl.NM → tl.gtTree.getD a 0 = tl.gtTree.getD b 0 → a = b)
    (hP : Powered tl theta)
    (h : neighboursDiffer
      ((rowAt (coefAll tl g F) (tl.gtTree.getD mu 0) 0).coef.toList.mergeSort le) = false) :
    ∃ i j, i < j ∧ j < (tl.shp.getD mu {}).mS ∧
      (Reading.gl.val theta ^ tl.stepF) ^ i = (Reading.gl.val theta ^ tl.stepF) ^ j := by
  rw [coef_mat tl g F hmu hr hinj] at h
  refine powers_of_no (tl.rowX.getD mu #[]).toList le (Reading.gl.val theta) tl.stepF
    (tl.shp.getD mu {}).mS (by rw [Array.length_toList, rowX_size hP hs]) (fun R hR => ?_) h
  rw [toList_getD]
  exact rowX_val hP hs hR

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.coef_mat
#print axioms VerifiableInference.Desc.First.K8.Honest.coef_powers
#print axioms VerifiableInference.Desc.First.K8.Honest.rowX_powers
#print axioms VerifiableInference.Desc.First.K8.Honest.rowX_val
#print axioms VerifiableInference.Desc.First.K8.Honest.differ_no_powers
