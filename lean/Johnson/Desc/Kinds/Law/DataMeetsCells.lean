-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/DataMeetsCells.lean: THE DATA THAT THE TABLE'S FORMS READ OFF A WITNESS AND
WHAT THE OUTPUT HEAD'S OWN LAW READS OFF IT MEET AT ONE TABLE ENTRY: second part: the cells. With it
the premise on symbols of Law/CellsOfData.lean (hsym) is paid at the seats off the layout
(Law/PlanK6At.lean: seatLay), from facts on public numbers and on the record's layout, frame,
statement and book.

THE HEART IS ANOTHER FILE'S: Johnson/Desc/First/Att/K05CellAt.lean: dataOf_cell: a cell of dataOf,
a sum over the layout's blocks, IS the table's entry at the place that the layout gives the element;
with laidPlace_one, laidIn_one, laidIn_row_lt, tableIndex_parts.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the theorems in Came).
  row_lt_of_ok: under the programs' own test on one array's layout the row that the layout gives an
      element is a row of the table.
  sym_of_data: AT ONE ELEMENT: the entry that the head's law reads by number at the seat off the
      layout (fLay) is the data's cell of the array that the label names.
  DataSeated ...: THE FACTS, GATHERED: for every matrix of segment 24, row of symbols and column in
      the four ranges: the layout has the array that the label names; it lays the element; the
      record's frame knows the array's message; the array passes the programs' test at that
      message's bits in the record's statement; the record's book seats the message at a seat of
      own, which is a tenant of segment 24's group, bears the message's number, and is the only
      tenant that does.
  comp_of_data: SO: compCut's cells and stream, at seat := seatLay, ARE cellsOfData's at the data
      read through the one accessor.

Every letter under "there is" (in DataSeated): A: pinned by the layout and the label; rp: by A and
the element; o: by the frame; x: by the book.
What it does not say. THAT DataSeated HOLDS AT ANY RECORD: of its clauses on the plan, that the
layout has the array and lays the element (by blocks, and at corners) and that one tenant bears the
number have been evaluated true at both stored plans on sheets, under riders; the
programs' test on the array's layout has not been run by us; its clauses
on the RECORD (that its layout is the plan's; its frame; its statement's bits; its book) are what
the table's promise must give at the border behind the block: NO LAW GIVES THEM HERE. Nothing on
soundness.
-/
import Johnson.Desc.First.Att.K05CellAt
import Johnson.Desc.Kinds.Law.DataMeets
import Johnson.Desc.Kinds.Law.CellsOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Params
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce)
open VerifiableInference.Desc.First.Att.P (dataOf_cell laidPlace_one laidIn_one laidIn_row_lt
  tableIndex tableIndex_parts)

namespace Came

/-- The row that the layout gives an element is a row of the table. -/
theorem row_lt_of_ok (A : ReqArray) (R P : Nat) (hok : laidMatrixOk A R P = true) (i c : Nat)
    (rp : Nat × Nat) (h : Desc.laidAt A i c = some rp) : rp.1 < 2 ^ R := by
  unfold laidMatrixOk at hok
  obtain ⟨hok1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hok
  obtain ⟨hall, _⟩ := Eq.mp (Bool.and_eq_true _ _) hok1
  unfold Desc.laidAt at h
  obtain ⟨b, hb, hbi⟩ := List.exists_of_findSome?_eq_some h
  have h1 := List.all_eq_true.1 hall b hb
  obtain ⟨h2, _⟩ := Eq.mp (Bool.and_eq_true _ _) h1
  obtain ⟨h3, _⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [laidIn_one] at hbi
  by_cases hh : First.Look.laidHolds b i c = true
  · rw [if_pos hh] at hbi
    rw [← Option.some.inj hbi]
    exact laidIn_row_lt b R P (K9L.blockFacts b _ _ h3) i c hh
  · rw [if_neg hh] at hbi
    exact nomatch hbi

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers)

/-- **At one element.** -/
theorem sym_of_data {Cells : Type} (own : List (Nat × Nat)) (a : K9.Part)
    (w : Wit Cells Tok MsgT) (num : Nat → Nat → Nat) (lab r c : Nat) (A : ReqArray)
    (rp : Nat × Nat) (o : Nat) (x : Nat × Nat)
    (hA : Desc.arrayOf a.L.check.rows.layout (Meaning.ownerK lab)
      (Meaning.nameOf (Meaning.ownerA lab)) = some A)
    (hl : Desc.laidAt A r c = some rp)
    (ho : a.L.check.frame.whereIs (Meaning.ownerK lab) A.message = some o)
    (hok : laidMatrixOk A (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true)
    (hx : K9.seatAt own a.d.book o = some x) (hg : x ∈ N.group 24)
    (hn : arr x.1 x.2 = num (Meaning.ownerK lab) A.message)
    (h1 : namedOnce arr N 24 (num (Meaning.ownerK lab) A.message) = true) :
    Sound.readAt cs arr msR N 24 w (Meaning.fLay a.L.check.rows.layout num lab r c).1 false
        (Meaning.fLay a.L.check.rows.layout num lab r c).2.1
        (Meaning.fLay a.L.check.rows.layout num lab r c).2.2 =
      (Sound.dataQ own a (Sound.seatTab cs arr msR w)).cell (Meaning.ownerK lab)
        (Meaning.nameOf (Meaning.ownerA lab)) r c := by
  have e : Meaning.fLay a.L.check.rows.layout num lab r c =
      (num (Meaning.ownerK lab) A.message, rp.1, rp.2) := by
    unfold Meaning.fLay Desc.seatIn
    rw [hA]
    show (((Desc.laidAt A r c).map fun x => (num (Meaning.ownerK lab) A.message, x.1, x.2)).getD
      (0, 0, 0)) = _
    rw [hl]
    rfl
  rw [e]
  show Sound.readAt cs arr msR N 24 w (num (Meaning.ownerK lab) A.message) false rp.1 rp.2 = _
  rw [readAt_at_seat cs arr msR N 24 _ w h1 x hg hn]
  unfold Sound.dataQ
  rw [dataOf_cell a.L.check.rows a.L.check.frame a.d.st _ (Meaning.ownerK lab)
    (Meaning.nameOf (Meaning.ownerA lab)) r c (a := A) (o := o) hA ho hok, laidPlace_one, hl]
  show _ = Sound.tabQ own a.d.st a.d.book (Sound.seatTab cs arr msR w) o .main
    (tableIndex (a.d.st.rowBits o .main) rp)
  unfold Sound.tabQ
  rw [hx]
  obtain ⟨t1, t2⟩ := tableIndex_parts (a.d.st.rowBits o .main) rp
    (row_lt_of_ok A _ _ hok r c rp hl)
  show _ = Sound.seatTab cs arr msR w x (OnBytes.Part.main == OnBytes.Part.mask)
    (tableIndex (a.d.st.rowBits o .main) rp % 2 ^ a.d.st.rowBits o .main)
    (tableIndex (a.d.st.rowBits o .main) rp / 2 ^ a.d.st.rowBits o .main)
  rw [t1, t2]
  rfl

end Came

/-- **The facts, gathered.** -/
def DataSeated (arr : Nat → Nat → Nat) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
    (own : List (Nat × Nat)) (a : K9.Part) (num : Nat → Nat → Nat) : Prop :=
  ∀ (μ : Fin (Meaning.sizesOf Wp 24).NM) (r c : Nat),
    r < Alg.symRows ((Meaning.sizesOf Wp 24).m μ) → c < (Meaning.sizesOf Wp 24).k μ →
    ColFour Wp.hS Wp.HLy (borderOf Wp.y) μ.val c →
    ∃ (A : ReqArray) (rp : Nat × Nat) (o : Nat) (x : Nat × Nat),
      Desc.arrayOf a.L.check.rows.layout (Meaning.ownerK (Meaning.labAt Wp 24 μ.val))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 μ.val))) = some A ∧
      Desc.laidAt A r c = some rp ∧
      a.L.check.frame.whereIs (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message = some o ∧
      laidMatrixOk A (a.d.st.rowBits o .main) (a.d.st.placeBits o .main) = true ∧
      K9.seatAt own a.d.book o = some x ∧ x ∈ N.group 24 ∧
      arr x.1 x.2 = num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message ∧
      namedOnce arr N 24 (num (Meaning.ownerK (Meaning.labAt Wp 24 μ.val)) A.message) = true

namespace Came

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **compCut's cells and stream are the data's.** -/
theorem comp_of_data (own : List (Nat × Nat)) (a : K9.Part) (num : Nat → Nat → Nat)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hD : DataSeated arr N Wp own a num) :
    (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp a.L.check.rows.layout num) Wp pl
        w).1.cell =
      (cellsOfData Wp (Meaning.sizesOf Wp)
        (Sound.dataQ own a (Sound.seatTab cs arr msR w))).cell ∧
    (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp a.L.check.rows.layout num) Wp pl
        w).1.stream =
      (cellsOfData Wp (Meaning.sizesOf Wp)
        (Sound.dataQ own a (Sound.seatTab cs arr msR w))).stream :=
  comp_of_syms cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp a.L.check.rows.layout num) Wp pl w _
    fun μ r c hr hc hcol => by
      obtain ⟨A, rp, o, x, hA, hl, ho, hok, hx, hg, hn, h1⟩ := hD μ r c hr hc hcol
      exact sym_of_data cs arr msR N own a w num (Meaning.labAt Wp 24 μ.val) r c A rp o x hA hl ho
        hok hx hg hn h1

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.row_lt_of_ok
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.sym_of_data
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.comp_of_data
