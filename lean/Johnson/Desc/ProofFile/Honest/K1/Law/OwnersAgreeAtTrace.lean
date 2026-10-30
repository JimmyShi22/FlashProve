-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/OwnersAgreeAtTrace.lean: THE ITEM
"tie m": A PAYER FOR THE PREMISE OwnersAgree
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanWide.lean), FROM THE TRACE, NOT LAID ANEW: at the
reference sizes Sz.ref, at the trace's own reader of cells cellsC X T
(Johnson/HonestTrace/DigitsAtTrace.lean), at the trace's files' list matsOf X l: under PartsFit X
(X's numbers of parts are 3, 1, 1, 4: public) and BorrowedSame X T (each borrowed matrix of T has
its owner's entries: three equations on T; Johnson/HonestTrace/CellOfOwner.lean). By the library's
sealed cellOf_owner. Six theorems; NO DEFINITION. X AND T ARE LETTERS: NO INPUT, NO PROVER, NO RUN,
NO COIN IS NAMED.
NO PROPERTY IS CLAIMED.

  - all_of_no_ref   the way back of the library's all_no_ref (Johnson/HonestTrace/FromCells.lean):
                  at the numbers of parts 3, 1, 1, 4 a name with the number a is member number a of
                  its segment's list.
  - matsOf_at   under PartsFit X: entry number mu of matsOf X at a segment's number: the owner's
                  number, the owner's label, the column 0.
  - ownersAgree_trace   THE PAYER: OwnersAgree Sz.ref (cellsC X T) (matsOf X l) l, at every l.
  - ownersAgree_of_reader   the like at any reader C whose cell IS cellOf X T.
  - ownersAgree_trace_own   the like at the place's own list, the lookups' matsOwn X l, for l < 25,
                  under PlanMarks X besides (public; by matsOwn_of_marks,
                  Johnson/HonestTrace/PlanLabelsOfMarks.lean).

  - ownersAgree_of_reader_own   both in one: at any such reader, at matsOwn X l:
                  exchangeAtS_tie_wide has ONE letter mats for hOwn and for its premise on the
                  reads, and that premise is typed at matsOwn.

OwnersAgree is one more debt of (P1)'s kind: what pays it comes from the trace:
ownersAgree_trace here, by cellOf_owner (Johnson/HonestTrace/CellOfOwner.lean),
under PartsFit and BorrowedSame, at Sz.ref; a premise laid anew pays nothing.

Limits. PartsFit, BorrowedSame AND PlanMarks ARE PREMISES: proved here of no X and no T (the
library's borrowedSame_of_meetsAll has BorrowedSame under MeetsAll X i x T, which it proves of
nothing). AT Sz.ref ALONE. WHAT STAYS OWED IN THE LAW exchangeAtS_tie_wide: there OwnersAgree
stands at the input's own cells under "valid": THAT THESE CELLS ARE A TRACE's (that (wit w).R.cells
has the cell cellOf X T at a T with BorrowedSame) IS A SENTENCE ON THE INPUT: NOT SAID HERE. From l
= 25 on Sz.ref has no segment: OwnersAgree holds there for nothing. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanWide
import Johnson.HonestTrace.CellOfOwner
import Johnson.HonestTrace.PlanLabelsOfMarks

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes
open OnBytes.HonestTrace (Sz Seg MatName Tr cellOf cellsC matsOf PartsFit BorrowedSame PlanMarks)
open ProofFile.Honest (Cells)

variable {X : Model.Verify.Public} {T : Tr}

/-- The way back of all_no_ref: at the numbers of parts 3, 1, 1, 4 a name with the number a is
member number a of its segment's list. -/
theorem all_of_no_ref (σ : Seg) {a : ℕ} {μ : MatName}
    (h : MatName.no? 3 1 1 4 σ μ = some a) : (MatName.all 3 1 1 4 σ)[a]? = some μ := by
  have e : (MatName.all 3 1 1 4 σ).length = Sz.ref.len σ := by cases σ <;> rfl
  have hlt : a < (MatName.all 3 1 1 4 σ).length := by
    rw [e]
    exact HonestTrace.no?_lt Sz.ref h
  have hν : (MatName.all 3 1 1 4 σ)[a]? = some ((MatName.all 3 1 1 4 σ)[a]) :=
    List.getElem?_eq_getElem hlt
  rw [hν, MatName.no?_inj (HonestTrace.all_no_ref σ hν) h]

/-- Under PartsFit X: entry number mu of the trace's files' list at a segment's number. -/
theorem matsOf_at (N : PartsFit X) {σ : Seg} (hσ : σ.Below 12) {mu : ℕ} {μ : MatName}
    (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) :
    (matsOf X (σ.no 12))[mu]? =
      some ((Sz.ref.owner σ μ).1.no 12, (Sz.ref.owner σ μ).2.label, 0) := by
  have ho := Seg.ofNo_no hσ
  have p1 := (HonestTrace.parts_at N ho).1
  unfold matsOf
  rw [ho]
  simp only [p1, List.getElem?_map, hμ, Option.map_some]

/-- **THE PAYER, FROM THE TRACE**: at the reference sizes, the trace's own reader and the trace's
files' list. -/
theorem ownersAgree_trace (N : PartsFit X) (Sm : BorrowedSame X T) (l : ℕ) :
    OwnersAgree Sz.ref (cellsC X T) (matsOf X l) l := by
  intro mu σ μ h
  obtain ⟨hσ, hno, hmu⟩ := (HonestTrace.matAt_eq_some_iff Sz.ref l mu σ μ).1 h
  have hσ' : σ.Below 12 := hσ
  have hn : MatName.no? 3 1 1 4 σ μ = some mu := by
    have : (if σ.Below 12 then MatName.no? 3 1 1 4 σ μ else none) = some mu := hmu
    rwa [if_pos hσ'] at this
  have hμ := all_of_no_ref σ hn
  obtain rfl : σ.no 12 = l := hno
  refine ⟨_, matsOf_at N hσ' hμ, fun r c _ _ => ?_⟩
  show cellOf X T ((Sz.ref.owner σ μ).1.no 12) (Sz.ref.owner σ μ).2.label r (0 + c) =
    cellOf X T (σ.no 12) μ.label r c
  rw [Nat.zero_add]
  exact (HonestTrace.cellOf_owner N Sm hσ' hμ r c).symm

/-- The like at any reader whose cell is the trace's reader's. -/
theorem ownersAgree_of_reader (N : PartsFit X) (Sm : BorrowedSame X T) {C : Cells}
    (hC : C.cell = cellOf X T) (l : ℕ) : OwnersAgree Sz.ref C (matsOf X l) l := by
  intro mu σ μ h
  obtain ⟨e, he, hh⟩ := ownersAgree_trace N Sm l mu σ μ h
  refine ⟨e, he, fun r c hr hc => ?_⟩
  rw [hC]
  exact hh r c hr hc

/-- The like at the place's own list, for l < 25, under PlanMarks X besides. -/
theorem ownersAgree_trace_own (Mk : PlanMarks X) (N : PartsFit X) (Sm : BorrowedSame X T) {l : ℕ}
    (hl : l < 25) : OwnersAgree Sz.ref (cellsC X T) (K3.matsOwn X l) l := by
  rw [HonestTrace.matsOwn_of_marks Mk N hl]
  exact ownersAgree_trace N Sm l

/-- **AT ANY READER WHOSE CELL IS THE TRACE's READER's, AT THE PLACE's OWN LIST**: the form to be
spent beside a law that has one letter for the list and is typed at matsOwn. -/
theorem ownersAgree_of_reader_own (Mk : PlanMarks X) (N : PartsFit X) (Sm : BorrowedSame X T)
    {C : Cells} (hC : C.cell = cellOf X T) {l : ℕ} (hl : l < 25) :
    OwnersAgree Sz.ref C (K3.matsOwn X l) l := by
  rw [HonestTrace.matsOwn_of_marks Mk N hl]
  exact ownersAgree_of_reader N Sm hC l

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.all_of_no_ref
#print axioms ProofFile.Honest.K1.matsOf_at
#print axioms ProofFile.Honest.K1.ownersAgree_trace
#print axioms ProofFile.Honest.K1.ownersAgree_of_reader
#print axioms ProofFile.Honest.K1.ownersAgree_trace_own
#print axioms ProofFile.Honest.K1.ownersAgree_of_reader_own
