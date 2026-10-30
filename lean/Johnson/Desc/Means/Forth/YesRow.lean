--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Forth/YesRow.lean: when the adding of a row to a group returns a state.

The IOP as written in Lean adds a row to a group by addRowP, and a list of rows by addRowsP
(Johnson/Desc/First/Base/Ground.lean). Each asks a list of named tests first. The laws beside that
file go backwards: what a call that returns gives. This file goes forwards: facts on a row (Fits)
under which the tests hold, so that the adding returns a state, which is written out.

Fits is the adding's own tests on the row, as statements: that the row is no sample row, that its
structured summands and its single entries fit their places. Two tests are cut down to "there is
none": runs and whole forms. One test is turned: the test on machine words, "no coefficient on an
entry that masks an answer", is asked as "the coefficient reads as 0 in the library's field". So
rowL_ok by itself pays for that one test and packs the others: they are shown only where Fits is.

Main names:
  Fits S G row        see above. S: the statement; G: the group
  rowL_ok             with the group there and in no proximity test, Fits gives all eight tests
  addRowP_of_fits     so the adding returns; the state behind is written out
  Fits.more, Fits.elsewhere   a further row on the group, or on any group, does not turn Fits
  addRowsFrom_of_fits, addRowsP_of_fits   so a list of such rows is added; the state behind is the
                      state in front with the rows appended (OnBytes.Slice.withRows)

What is not claimed. Which rows meet Fits. Rows with runs or whole forms are not served. Nothing on
what a row means, on soundness, on completeness or on hiding.

-/
import Johnson.Desc.Means.Forth.YesWords
import Johnson.Desc.First.Base.Ground
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open Desc.Plain (DState)
open VerifiableInference.Desc.Ground (addRowP addRowsP addRowsFrom rowL rowsL ok)

/-- **Facts on a row under which a group takes it.** S: the statement; G: the group. -/
structure Fits (S : Statement) (G : Group) (row : Row) : Prop where
  kind : row.kind ≠ .sample
  terms : ∀ t ∈ row.terms, VerifiableInference.Desc.Own.tensorInOrder t.v = true ∧
    VerifiableInference.Desc.Own.placeFits S G t.oracle t.part t.v.vars 0 = true
  units : ∀ u ∈ row.units, VerifiableInference.Desc.Own.placeFits S G u.oracle u.part
    (S.tableBits u.oracle u.part) u.index = true
  runs : row.runs = #[]
  forms : row.forms = #[]
  /-- on an entry that masks a member's answer the coefficient reads as 0 -/
  pads : ∀ o ∈ G.members, ∀ x, S.oracles[o]? = some x → ∀ q ∈ x.pad,
    Model.Reading.gl.val (row.coefficient o q.1 q.2) = 0

/-- With the group there and in no proximity test, Fits gives all eight tests of the adding. -/
theorem rowL_ok (S : Statement) (g : Nat) (G : Group) (row : Row) (hG : S.groups[g]? = some G)
    (hrun : G.inRun = false) (h : Fits S G row) : ok (rowL S g row) = true := by
  simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [hG]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (!G.inRun) = true
    rw [hrun]
    rfl
  · simpa using h.kind
  · show (row.terms.all fun t => VerifiableInference.Desc.Own.tensorInOrder t.v &&
      VerifiableInference.Desc.Own.placeFits S G t.oracle t.part t.v.vars 0) = true
    rw [Array.all_eq_true_iff_forall_mem]
    intro t ht
    rw [Bool.and_eq_true]
    exact h.terms t ht
  · show (row.units.all fun u => VerifiableInference.Desc.Own.placeFits S G u.oracle u.part
      (S.tableBits u.oracle u.part) u.index) = true
    rw [Array.all_eq_true_iff_forall_mem]
    exact h.units
  · show (row.runs.all _) = true
    rw [Array.all_eq_true_iff_forall_mem]
    intro w hw
    rw [h.runs] at hw
    simp at hw
  · show (row.forms.all _) = true
    rw [Array.all_eq_true_iff_forall_mem]
    intro f hf
    rw [h.forms] at hf
    simp at hf
  · show (G.members.all fun o => (((S.oracles[o]?).map (·.pad)).getD []).all fun q =>
      VerifiableInference.Desc.Own.allZero (row.coefficient o q.1 q.2)) = true
    rw [Array.all_eq_true_iff_forall_mem]
    intro o ho
    cases hx : S.oracles[o]? with
    | none => rfl
    | some x =>
      show (x.pad.all fun q =>
        VerifiableInference.Desc.Own.allZero (row.coefficient o q.1 q.2)) = true
      rw [List.all_eq_true]
      intro q hq
      exact allZero_coefficient row o q.1 q.2 (h.pads o ho x hx q hq)

/-- **The adding of a row that fits returns**; the state behind is written out. -/
theorem addRowP_of_fits {L : Type} (d : DState L) (g : Nat) (G : Group) (row : Row)
    (hG : d.st.groups[g]? = some G) (hrun : G.inRun = false) (h : Fits d.st G row) :
    addRowP d g row = some { d with st := Slice.withRow d.st g row } := by
  unfold addRowP
  rw [if_pos (rowL_ok d.st g G row hG hrun h)]

/-- A further row on the group does not turn Fits. -/
theorem Fits.more {S : Statement} {G : Group} {row : Row} (h : Fits S G row) (g : Nat)
    (r : Row) : Fits (Slice.withRow S g r) { G with rows := G.rows.push r } row :=
  ⟨h.kind, fun t ht => h.terms t ht, fun u hu => h.units u hu, h.runs, h.forms,
    fun o ho x hx q hq => h.pads o ho x hx q hq⟩

/-- A further row on any group does not turn Fits. -/
theorem Fits.elsewhere {S : Statement} {G : Group} {row : Row} (h : Fits S G row) (g : Nat)
    (r : Row) : Fits (Slice.withRow S g r) G row :=
  ⟨h.kind, fun t ht => h.terms t ht, fun u hu => h.units u hu, h.runs, h.forms,
    fun o ho x hx q hq => h.pads o ho x hx q hq⟩

/-- Rows that fit are added one by one. -/
theorem addRowsFrom_of_fits {L : Type} (g : Nat) : ∀ (rows : List Row) (d : DState L) (G : Group),
    d.st.groups[g]? = some G → G.inRun = false → (∀ row ∈ rows, Fits d.st G row) →
    addRowsFrom g rows d = some { d with st := Slice.withRows d.st g rows }
  | [], _, _, _, _, _ => rfl
  | row :: rows, d, G, hG, hrun, h => by
    have h1 := addRowP_of_fits d g G row hG hrun (h row List.mem_cons_self)
    have h2 := addRowsFrom_of_fits g rows { d with st := Slice.withRow d.st g row }
      { G with rows := G.rows.push row } (Slice.withRow_group d.st g row G hG) hrun
      (fun r hr => (h r (List.mem_cons_of_mem _ hr)).more g row)
    show (addRowP d g row).bind (addRowsFrom g rows) = _
    rw [h1]
    exact h2

/-- **The adding of a list of rows that fit returns**; the state behind is written out. -/
theorem addRowsP_of_fits {L : Type} (d : DState L) (g : Nat) (G : Group) (rows : List Row)
    (hG : d.st.groups[g]? = some G) (hrun : G.inRun = false)
    (h : ∀ row ∈ rows, Fits d.st G row) :
    addRowsP d g rows = some { d with st := Slice.withRows d.st g rows } := by
  have hok : ok (rowsL d.st g) = true := by
    simp only [ok, rowsL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [hG]
    refine ⟨rfl, ?_⟩
    show (!G.inRun) = true
    rw [hrun]
    rfl
  unfold addRowsP
  rw [if_pos hok]
  exact addRowsFrom_of_fits g rows d G hG hrun h

end OnBytes.Means

#print axioms OnBytes.Means.rowL_ok
#print axioms OnBytes.Means.addRowP_of_fits
#print axioms OnBytes.Means.Fits.more
#print axioms OnBytes.Means.Fits.elsewhere
#print axioms OnBytes.Means.addRowsFrom_of_fits
#print axioms OnBytes.Means.addRowsP_of_fits
