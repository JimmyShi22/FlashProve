-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/RowLFull.lean: MEMBERS OF RowL's TEST (`rowLB`), BY EVALUATION IN LEAN's KERNEL, AT THE FULL SIZE's WRITTEN LIST OF PLACES (First.flatPlacesOf linksFull true): at all
twenty-five digits' places (moment 2; no tied public item comes) and at all twenty-five reads' places (moment 1; the tied public items that come: tiedAt). AND THAT THE TEST CAN FAIL.
  tiedAt links ps k      the tied public items that are asked behind block k and not in front. AT T := tiedAt THE TEST's LAST CLAUSE IS TRUE BY CONSTRUCTION: its weight lies in the premise hpub
  rowLB_digits_full · rowLB_reads_full     [kernel] · tiedAt_counts [kernel]: some come at every reads' row, none at a digits' row
  k01_later_places       [kernel] at the number 14 l + k1Ix l d + 2 the written list has K1's address ⟨1, some l, k1Ix l d + 1, K1⟩
  laysNone_full          [kernel] the table's rows there lay nothing and are filled · rowSegs_full [kernel]: the segments with an open class of rows there are at most l
  rowLB_fails            at another moment · one block on · at another segment: false [kernel]
  rowL_digits_full · rowL_reads_full       so RowL, at every N and M with the three premises of rowL_of_test, at the list that comes ++ what the door's filling makes there
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.RowLTest
import Johnson.IMR.K1Scope
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open IM (k1Ix)

/-- The tied public items that come at block k. -/
def tiedAt (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  (First.pubOfItems (openAt links ps (k + 1))).filter
    fun q => !(First.pubOfItems (openAt links ps k)).contains q

theorem rowLB_digits_full : ((List.range 25).all fun l =>
    rowLB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2) l 2 []) = true := by
  decide +kernel

theorem rowLB_reads_full : ((List.range 25).all fun l =>
    rowLB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) l 1
      (tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2))) = true := by
  decide +kernel

/-- The reads' rows bring tied public items; the digits' rows none. -/
theorem tiedAt_counts : ((List.range 25).map fun l =>
    ((tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)).length,
      (tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2)).length)).all
      (fun x => decide (0 < x.1) && x.2 == 0) = true := by
  decide +kernel

/-- **At the fifty numbers the written list has K1's later addresses**: link l; piece k1Ix l d + 1; the kind K1. -/
theorem k01_later_places : ((List.range 25).all fun l => [false, true].all fun d =>
    decide ((flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]? = some (IM.k1PlaceL l d))) = true := by
  decide +kernel

/-- **The table's rows at the fifty places lay nothing** (the field `lays`: "its extractor lays components of the witness (else it is the identity)"), and are filled. -/
theorem laysNone_full : ((List.range 25).all fun l => [false, true].all fun d =>
    !(First.rowOf linksFull (IM.k1PlaceL l d)).lays && (First.rowOf linksFull (IM.k1PlaceL l d)).known) =
      true := by
  decide +kernel

/-- The segments with an open class of rows behind a later place of link l: which. -/
theorem rowSegs_full : ((List.range 25).all fun l => [false, true].all fun d =>
    (First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2 + 1))).all
      fun m' => decide (m' ≤ l)) = true := by
  decide +kernel

/-- **The test can fail.** -/
theorem rowLB_fails :
    rowLB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2) 3 1 [] = false ∧
    rowLB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 3) 3 2 [] = false ∧
    rowLB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2) 4 2 [] = false ∧
    rowLB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 2) 3 1 [] = false := by
  decide +kernel

theorem rowL_digits_full (N : Numbers) (M : More) (l : ℕ) (hl : l < 25) (nT nM : ℕ)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l true + 2 + 1)), N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l true + 2 + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l true + 2]? + nT)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[14 * l + k1Ix l true + 2 + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[14 * l + k1Ix l true + 2]? + nM) :
    RowL N M linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2) l 2 nT nM
      ([] ++ madeAt M linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2)) :=
  rowL_of_test N M _ _ _ l 2 nT nM []
    (List.all_eq_true.1 rowLB_digits_full l (List.mem_range.2 hl)) hinj trees msgs

theorem rowL_reads_full (N : Numbers) (M : More) (l : ℕ) (hl : l < 25) (nT nM : ℕ)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l false + 2 + 1)), N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2 + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]? + nT)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2 + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]? + nM) :
    RowL N M linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) l 1 nT nM
      (tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) ++
        madeAt M linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)) :=
  rowL_of_test N M _ _ _ l 1 nT nM _
    (List.all_eq_true.1 rowLB_reads_full l (List.mem_range.2 hl)) hinj trees msgs

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.rowLB_digits_full
#print axioms VerifiableInference.Desc.K1.rowLB_reads_full
#print axioms VerifiableInference.Desc.K1.tiedAt_counts
#print axioms VerifiableInference.Desc.K1.k01_later_places
#print axioms VerifiableInference.Desc.K1.laysNone_full
#print axioms VerifiableInference.Desc.K1.rowSegs_full
#print axioms VerifiableInference.Desc.K1.rowLB_fails
#print axioms VerifiableInference.Desc.K1.rowL_digits_full
#print axioms VerifiableInference.Desc.K1.rowL_reads_full
