-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/DoorTests.lean
(kind K9's soundness lemma): THEOREMS: K9's DOOR LAYS ITS ROW BY THE GROUND's
addRowP, so all tests of a new open row have said yes of it.
  RowClauses    the tests of a new open row (Ground.rowL, behind "the group is there"), as
                sentences: no proximity test of the group has begun · no sample row · its terms,
                single entries, runs and forms fit their places (the library's Blk.placeOk: a member
                of the group; the table is there; the variables are the table's bits; the index is
                within the table) · it has no coefficient on a pad.
  rowL_clauses  a yes of Ground.rowL gives the group and RowClauses.
  door_addRowP  where K9.door returns, its record is what Ground.addRowP made of the record behind
                K9.asRow and the row of K9.asRow.
  door_tests    **where K9.door returns: the record behind it is the record d1 behind K9.asRow with
                the row laid (Slice.withRow); the segment's group is there at d1, and is the group
                in front of the door; RowClauses holds of the row at d1's statement.**
Not claimed: anything on what a later block does with the row.

-/
import Johnson.Desc.First.Batch.Law.RowFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Ans Equation equation asRow St door)

/-- The tests of a new open row on the group G, as sentences. -/
structure RowClauses (S : Statement) (G : Group) (row : OnBytes.Row) : Prop where
  noTest : G.inRun = false
  noSample : row.kind ≠ .sample
  terms : ∀ t ∈ row.terms, t.v.ok = true ∧ Blk.placeOk S G t.oracle t.part t.v.vars 0 = true
  units : ∀ u ∈ row.units,
    Blk.placeOk S G u.oracle u.part (S.tableBits u.oracle u.part) u.index = true
  runs : ∀ w ∈ row.runs, w.coeffs.ok = true ∧ 0 < w.coeffs.size ∧ 1 ≤ w.step ∧
    Blk.placeOk S G w.oracle w.part (S.tableBits w.oracle w.part)
      (w.first + w.step * (w.coeffs.size - 1)) = true
  forms : ∀ f ∈ row.forms,
    Blk.placeOk S G f.oracle .main (S.tableBits f.oracle .main) 0 = true ∧
      f.c.fits (S.tableBits f.oracle .main) = true
  pads : ∀ o ∈ G.members, ∀ q ∈ ((S.oracles[o]?).map (·.pad)).getD [],
    isZeroE (row.coefficient o q.1 q.2) = true

/-- A yes of the ground's test of a new open row. -/
theorem rowL_clauses (S : Statement) (g : Nat) (row : OnBytes.Row)
    (h : Ground.ok (Ground.rowL S g row) = true) :
    ∃ G, S.groups[g]? = some G ∧ RowClauses S G row := by
  simp only [Ground.ok, Ground.rowL, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.and_true, ← Own.tensorInOrder_agrees, ← Own.placeFits_agrees,
    ← Own.coeffsInside_agrees, ← Own.formFits_agrees, ← Own.allZero_agrees] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.mp h1
  simp only [Ground.has, hG, Option.map_some, Option.getD_some] at h2 h4 h5 h6 h7 h8
  simp only [Array.all_eq_true_iff_forall_mem, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h4 h5 h6 h7 h8
  exact ⟨G, hG, by simpa using h2, by simpa using h3, h4, h5,
    fun w hw => ⟨(h6 w hw).1.1.1, (h6 w hw).1.1.2, (h6 w hw).1.2, (h6 w hw).2⟩, h7, h8⟩

/-- The door lays its row by the ground's addRowP. -/
theorem door_addRowP {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    ∃ q G row d1, equation L F = .ok (q, G) ∧
      asRow L.check.rows L.check.frame q d = .ok (row, d1) ∧
      Ground.addRowP d1 L.check.group row = some out.d := by
  unfold door at h
  obtain ⟨n, _, h⟩ := ok_bind h
  obtain ⟨x, hx, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨_, _, h⟩ := ok_bind h
  obtain ⟨y, hy, h⟩ := ok_bind h
  obtain ⟨d2, hd, h⟩ := ok_bind h
  have e := Except.ok.inj h
  refine ⟨x.1, x.2, y.1, y.2, hx, hy, ?_⟩
  rw [← e]
  exact there_ok hd

/-- **The door's row has passed all tests of a new open row.** -/
theorem door_tests {X : Type} (owed laid : Option Nat) (L : LinkCtx) (F : Fork) (d : St X)
    (out : K9.Out X) (h : door owed laid L F d = .ok out) :
    ∃ (row : OnBytes.Row) (d1 : St X) (G0 : Group),
      out.d = { d1 with st := Slice.withRow d1.st L.check.group row } ∧
      d1.st.groups[L.check.group]? = some G0 ∧ d.st.groups[L.check.group]? = some G0 ∧
      RowClauses d1.st G0 row := by
  obtain ⟨q, G, row, d1, _, hr, ha⟩ := door_addRowP owed laid L F d out h
  unfold Ground.addRowP at ha
  split at ha
  · rename_i hok
    obtain ⟨G0, hG, hc⟩ := rowL_clauses _ _ _ hok
    refine ⟨row, d1, G0, (Option.some.inj ha).symm, hG, ?_, hc⟩
    rw [← asRow_groups _ _ _ _ _ _ hr]
    exact hG
  · simp at ha

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.rowL_clauses
#print axioms VerifiableInference.Desc.K9L.door_addRowP
#print axioms VerifiableInference.Desc.K9L.door_tests
