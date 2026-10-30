-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/FromTheCut.lean: FROM ONE TEST ON PUBLIC VALUES, h : cutOf bs =
cutFirstFull (the cut of the first chain's sub-protocols is the written cut:
Johnson/Desc/Ok/PlanWritten/CutTest.lean, CutLit.lean), TO WHAT THE PREMISES OF THE KIND K1's LAW's
TOP SPEND OF "what the sub-protocols declare": named lemmas, in the letters of the binders. A
joining of what lies. A law file; no running text imports it.
  told_of_cut, toldBy_of_cut: what the sub-protocols declare is toldC: in two spellings:
      First.toldOf (NumbersAtBlocks.lean) and Sound.toldBy (BaseOfBookFit.lean)
  oracles_flat, oracles_of_cut: their oracles, one list, are osC
  fits_of_cut: so the field fits of PlanAt at the written seats (fits_full's one premise is paid)
  trees_at_of_counts: the trees in front of a border, off the written counts: over letters
  trees_of_cut, trees_two_of_cut: so the number of trees in front of each of the fifty later
      places is 3 * l + moment + 1, of the opening 0, of W's sending 82: at every N.withTold psF
      (First.toldOf bs)
  later_place, parL_place: a later place at the first chain's parameters q, gp is placeL l d, where
      q has the written codes and shape and gp = ⟨1, 0⟩; the like in the top's own letter parL Z G l
      d
  laid_getD: (iv) of the field told in the form in which hTold_at asks it
  h4_of: hTold_at's premise h4, to its letter but for the base: at every base b l d with b l d = 3
      * l + moment + 1

WHAT STAYS: h itself (by report other files have "laid gives the pins' accept and the cut");
the base's tie to N.treesAt (baseL_at); hc, hs, hg (in scope
under the door's pin). Nothing on soundness.

-/
import Johnson.Desc.AtSeats.PlanRestAtCut
import Johnson.Desc.AtSeats.FitsAtPlan
import Johnson.HB.LLHARD.CountsAtCut
import Johnson.Desc.First.CutAtNumbers
import Johnson.Goal.Numbers.RequestWritten
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.Sound.BaseOfBookFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc (Block FileDescription oraclesOf osC fits_full)
open VerifiableInference.Desc.First (Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull SeatFits msOf toldBy)
open VerifiableInference.Desc.K13.Law (countsFull CountsAre countsAre_cut told_at)
open VerifiableInference.PlanWritten (cutOf cutFirstFull proofSizedFull)
open HashBuild (toldC psF laidFull)
open Johnson.G (codesFull2)
open IM (k1Ix)

section
variable {St Cl : Type} {bs : List (Block St Cl)}

/-- **What the sub-protocols declare is the written cut's.** -/
theorem told_of_cut (h : cutOf bs = cutFirstFull) : First.toldOf bs = toldC := by
  rw [First.toldOf_cut, h]
  rfl

theorem toldBy_is (bs : List (Block St Cl)) : toldBy bs = First.toldOf bs := by
  unfold toldBy First.toldOf
  exact List.map_congr_left fun _ _ => List.flatMap_id

theorem toldBy_of_cut (h : cutOf bs = cutFirstFull) : toldBy bs = toldC :=
  (toldBy_is bs).trans (told_of_cut h)

theorem oracles_flat (bs : List (Block St Cl)) : oraclesOf bs = (toldBy bs).flatten := by
  unfold oraclesOf toldBy
  exact List.flatMap_def

/-- **Their oracles, one list.** -/
theorem oracles_of_cut (h : cutOf bs = cutFirstFull) : oraclesOf bs = osC := by
  rw [oracles_flat, toldBy_of_cut h]
  rfl

theorem counts_of_cut (h : cutOf bs = cutFirstFull) : CountsAre (First.toldOf bs) := by
  rw [told_of_cut h]
  exact countsAre_cut

/-- The trees in front of a border, off the written counts: over letters. -/
theorem trees_at_of_counts (h : cutOf bs = cutFirstFull) (N : Numbers) {k t : ℕ} (hk : k ≤ 358)
    (hc : (countsFull[k]?).map (·.2) = some t) :
    (N.withTold (flatPlacesOf linksFull true) (First.toldOf bs)).treesAt
      (flatPlacesOf linksFull true)[k]? = t := by
  rw [told_at N (counts_of_cut h) hk] at hc
  exact Option.some.inj hc

/-- **The trees in front of each of the fifty.** -/
theorem trees_of_cut (h : cutOf bs = cutFirstFull) (N : Numbers) (l : ℕ) (hl : l < 25) (d : Bool) :
    (N.withTold (flatPlacesOf linksFull true) (First.toldOf bs)).treesAt
      (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]? = baseL3 l d := by
  have hk : 14 * l + k1Ix l d + 2 ≤ 358 := by
    have : k1Ix l d ≤ 6 := by
      unfold k1Ix
      split <;> split <;> omega
    omega
  exact trees_at_of_counts h N hk (eq_of_beq (fifty_of bases_counts l hl d))

theorem trees_two_of_cut (h : cutOf bs = cutFirstFull) (N : Numbers) :
    (N.withTold (flatPlacesOf linksFull true) (First.toldOf bs)).treesAt
        (flatPlacesOf linksFull true)[2]? = 0 ∧
      (N.withTold (flatPlacesOf linksFull true) (First.toldOf bs)).treesAt
        (flatPlacesOf linksFull true)[356]? = 82 := by
  have hb := bases_two
  injection hb with e2 hr
  injection hr with e356 _
  exact ⟨trees_at_of_counts h N (by omega) e2, trees_at_of_counts h N (by omega) e356⟩

end

/-- **The field fits at the written seats, from the cut.** -/
theorem fits_of_cut {Xi : Type} (G : FileDescription Xi) (radM : ℕ → ℕ → ℕ) {n : ℕ}
    (hn : ∀ p ∈ P5T.psFull, p.smpd = true → p.send < n) (h : cutOf G.first.blocksInOrder = cutFirstFull) :
    ∀ x ∈ msOf (P5T.memberListsR n radM P5T.psFull), SeatFits G codesFull2 x.1.l x.1.seat :=
  fits_full G radM hn (oracles_of_cut h)

/-! ## The places -/

theorem later_place {q : Params.First} {gp : _root_.Desc.Plain.GPar} (hc : q.codes = codesFull2)
    (hs : q.shape = ReqLit.shapeFull) (hg : gp = ⟨1, 0⟩) (l : ℕ) (d : Bool) :
    parLater q gp l (k1Ix l d + 1) (cond d 2 1) = placeL l d := by
  rw [hg]
  exact parLater_congr hc
    (hs.trans VerifiableInference.PlanWritten.request_shape_written.symm) _ _ _ _

theorem parL_place {Z : ProofFile.Pub} {G : ProofFile.Ground} (hc : G.first.codes = codesFull2)
    (hs : G.first.shape = ReqLit.shapeFull) (hg : gpOf Z = ⟨1, 0⟩) (l : ℕ) (d : Bool) :
    parL Z G l d = placeL l d := by
  cases d with
  | true => exact later_place hc hs hg l true
  | false => exact later_place hc hs hg l false

/-! ## h4 -/

theorem laid_getD (l : ℕ) (hl : l < 25) (d : Bool) (n : ℕ)
    (hn : n < (layOf (placeL l d)).shapes.size) :
    laidFull[baseL3 l d + n]? = some (((layOf (placeL l d)).shapes.getD n {}).logN,
      ((layOf (placeL l d)).shapes.getD n {}).mainWidth +
        ((layOf (placeL l d)).shapes.getD n {}).maskWidth) := by
  rw [laid_at l hl d n hn, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hn]
  rfl

/-- **hTold_at's h4**, at every base that is the numeral. -/
theorem h4_of {Z : ProofFile.Pub} {G : ProofFile.Ground} (hc : G.first.codes = codesFull2)
    (hs : G.first.shape = ReqLit.shapeFull) (hg : gpOf Z = ⟨1, 0⟩) (b : ℕ → Bool → ℕ)
    (hb : ∀ l, l < 25 → ∀ d, b l d = baseL3 l d) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ n, n < (layOf (parL Z G l d)).shapes.size →
      laidFull[b l d + n]? = some (((layOf (parL Z G l d)).shapes.getD n {}).logN,
        ((layOf (parL Z G l d)).shapes.getD n {}).mainWidth +
          ((layOf (parL Z G l d)).shapes.getD n {}).maskWidth) := by
  intro l hl d n hn
  rw [parL_place hc hs hg l d] at hn ⊢
  rw [hb l hl d]
  exact laid_getD l hl d n hn

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.told_of_cut
#print axioms VerifiableInference.Desc.K1.toldBy_of_cut
#print axioms VerifiableInference.Desc.K1.oracles_of_cut
#print axioms VerifiableInference.Desc.K1.trees_of_cut
#print axioms VerifiableInference.Desc.K1.trees_two_of_cut
#print axioms VerifiableInference.Desc.K1.fits_of_cut
#print axioms VerifiableInference.Desc.K1.later_place
#print axioms VerifiableInference.Desc.K1.parL_place
#print axioms VerifiableInference.Desc.K1.laid_getD
#print axioms VerifiableInference.Desc.K1.h4_of
