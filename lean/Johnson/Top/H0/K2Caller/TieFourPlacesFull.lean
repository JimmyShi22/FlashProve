-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/TieFourPlacesFull.lean: code switching: AT THE FULL SIZE's WRITTEN LIST OF
PLACES (flatPlacesOf linksFull true; linksFull: Johnson/Desc/Sound/AtDriver.lean) EVERY PLACE OF THE
KIND K2 HAS A SEGMENT m IN FRONT, ITS ROW OF THE TABLE OF JOINTS CLOSES JUST «carry m» AND
«pinKept m», READS NOTHING MORE, AND LAYS: by Lean's kernel. So the m of the fourth tie at a place
(k02_t4R, K2Caller/TieFourR.lean: its binder hins) is the m of TieFourPadsAtPlan.lean's two premises
on the place. One test with code, five theorems. NO SUB-PROTOCOL IMPORTS THIS FILE.
  k2RowB links p      the test at a place: not of the kind K2; or, with l its segment's number (the
                      number of segments where it has none): 1 ≤ l ≤ the number of segments, the
                      row's ins are [carry (l - 1), pinKept (l - 1)], its ctx is empty, it lays
  k2Row_of_B          what a pass gives at a place of the kind: an m with all of it
  k2Rows_full         the kernel's yes at all places of the full list
  k2Links_are         the places of the kind K2 of the full list have the numbers 1, 2, …, 25, in
                      this order: so the test asks something at 25 places, and the last code switch
                      is counted
  k2_row_full         at sub-protocol number k of the full list, where the place is of the kind:
                      there is an m below 25 with l = m + 1, the tie's binders hins and hctx at this
                      m, and «the row lays»
  k2_m_full           THE SPENDER's FORM: whichever m the tie's hins holds at is that m: m < 25,
                      l = m + 1, and the row lays
LIMITS. Of the written list alone: that the places of the IOP as written in Lean are this list is
another file's (placesFit). Nothing on the small size. No soundness is claimed. On hiding nothing.

-/
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound (linksFull rowQ)
open VerifiableInference.Desc.First (ModelPart Item flatPlacesOf rowOf)

/-- **The test at a place.** -/
def k2RowB (links : List ModelPart) (p : Place) : Bool :=
  p.kind != .K2 ||
    (decide (1 ≤ p.link.getD links.length) && decide (p.link.getD links.length ≤ links.length) &&
      decide ((rowOf links p).ins =
        [.carry (p.link.getD links.length - 1), .pinKept (p.link.getD links.length - 1)]) &&
      decide ((rowOf links p).ctx = []) && (rowOf links p).lays)

/-- **What a pass gives at a place of the kind.** -/
theorem k2Row_of_B {links : List ModelPart} {p : Place} (h : k2RowB links p = true)
    (hk : p.kind = .K2) : ∃ m, m < links.length ∧ p.link.getD links.length = m + 1 ∧
      (rowOf links p).ins = [.carry m, .pinKept m] ∧ (rowOf links p).ctx = [] ∧
      (rowOf links p).lays = true := by
  unfold k2RowB at h
  rw [hk] at h
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨p.link.getD links.length - 1, by omega, by omega, h3, h4, h5⟩

set_option maxRecDepth 100000 in
/-- The kernel's yes at all places of the full list. -/
theorem k2Rows_full : (flatPlacesOf linksFull true).all (k2RowB linksFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The places of the kind K2 of the full list have the numbers 1 to 25, in this order. -/
theorem k2Links_are : ((flatPlacesOf linksFull true).filter fun p => p.kind == .K2).map
    (fun p => p.link.getD linksFull.length) = List.range' 1 25 := by
  decide +kernel

/-- **At a sub-protocol of the kind K2 of the full list**: a segment in front, the tie's two binders
on the table's row, and «the row lays». -/
theorem k2_row_full (k : ℕ) (p : Place) (hp : (flatPlacesOf linksFull true)[k]? = some p)
    (hk : p.kind = .K2) : ∃ m, m < linksFull.length ∧ p.link.getD linksFull.length = m + 1 ∧
      (rowQ linksFull (flatPlacesOf linksFull true) k).ins = [.carry m, .pinKept m] ∧
      (rowQ linksFull (flatPlacesOf linksFull true) k).ctx = [] ∧
      (rowOf linksFull p).lays = true := by
  have e : rowQ linksFull (flatPlacesOf linksFull true) k = rowOf linksFull p := by
    unfold rowQ
    rw [hp]
    rfl
  rw [e]
  exact k2Row_of_B (List.all_eq_true.1 k2Rows_full p (List.mem_of_getElem? hp)) hk

/-- **The spender's form**: the m at which the tie's binder hins holds is the segment in front. -/
theorem k2_m_full (k m : ℕ) (p : Place) (hp : (flatPlacesOf linksFull true)[k]? = some p)
    (hk : p.kind = .K2)
    (hins : (rowQ linksFull (flatPlacesOf linksFull true) k).ins = [.carry m, .pinKept m]) :
    m < linksFull.length ∧ p.link.getD linksFull.length = m + 1 ∧
      (rowOf linksFull p).lays = true := by
  obtain ⟨m', h1, h2, h3, -, h5⟩ := k2_row_full k p hp hk
  rw [h3] at hins
  have e : m' = m := by
    have e1 := (List.cons.inj hins).1
    exact Item.carry.inj e1
  subst e
  exact ⟨h1, h2, h5⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Row_of_B
#print axioms VerifiableInference.Desc.First.K2Caller.k2Rows_full
#print axioms VerifiableInference.Desc.First.K2Caller.k2Links_are
#print axioms VerifiableInference.Desc.First.K2Caller.k2_row_full
#print axioms VerifiableInference.Desc.First.K2Caller.k2_m_full
