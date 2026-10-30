-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LaidCovered.lean: under the programs' test on a layout an array answers at
every one of its elements; so the test laidThere needs no walk over the elements. Theorems, proved;
one definition with code.

Why. laidThere (Johnson/Goal/Meaning/HidSeatsOf.lean) bars the silent seat (0, 0, 0): for every
entry of the 25 lists the array that its label names is there, has the entry's rows and columns, AND
IS LAID AT EVERY ELEMENT: two loops over all elements. The programs' test on a layout has that last
clause by counting (laidMatrixOk, OnBytes/Iop/ReqRows.lean: the blocks lie inside the matrix, no two
share an element, and their sizes add up to the matrix's). The counting itself is proved in
Johnson/Desc/First/Look/K3CallerLaid.lean (cover_all, pairwise_of_noPair, disjoint_of_meetB), under
a test of that file's own. Here it is called at the programs' test: no counting is done again.

Main names:
  laidAt_of_matrixOk   THE COVERING: laidMatrixOk a R T = true, i < a.sizeI, c < a.sizeC: then
    laidAt a i c answers.
  matrix_of_message, laidAt_of_layout   the same from reqLayoutOk, at an array of a link.
  namedThere X s layout   a test with code: laidThere without its two inner loops.
  laidThere_of_named   reqLayoutOk codes shape layout = true and namedThere X s layout = true give
    laidThere X s layout = true.

Object, user, letters. laidAt_of_matrixOk: object laidMatrixOk, laidAt; user laidAt_of_layout; all
letters free. laidThere_of_named: object reqLayoutOk, laidThere; user: none in the library yet; it
fits the premise T of seat_inside and seat_inside_members
(Johnson/Goal/Meaning/LaidInsideSeats.lean); codes, shape, layout, X, s free.

What is not claimed. That two elements have two seats. namedThere, or reqLayoutOk, at any plan: none
has run here. reqLayoutOk wants every array to have a row and a column: where a list has an entry
with no row of symbols or no column, it and namedThere cannot both say yes; that no such entry
stands in the 25 lists is not shown here. Nothing on soundness, nothing on hiding. The program does
not import this file.
-/
import Johnson.Goal.Meaning.LaidInside
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Desc.First.Look.K3CallerLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes
open OnBytes.Params (LaidBlock ReqArray ReqLayout ReqShape)
open VerifiableInference.Desc (laidIn laidAt arrayOf)
open VerifiableInference.Desc.First.Look (laidHolds holds_iff cover_all pairwise_of_noPair meetB
  disjoint_of_meetB)
open Cb.Pv.Tail (Size)

/-- Where a block of the array holds the element, the array answers. -/
theorem laidAt_of_holds {A : ReqArray} {b : LaidBlock} (hb : b ∈ A.blocks) {i c : ℕ}
    (h : laidHolds b i c = true) : (laidAt A i c).isSome = true := by
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := holds_iff.1 h
  unfold laidAt
  rw [List.findSome?_isSome_iff]
  refine ⟨b, hb, ?_⟩
  unfold laidIn
  rw [if_pos ⟨a1, a2, a3, a4⟩]
  rfl

/-- **THE COVERING.** Under the programs' test on one matrix the array answers at every element. -/
theorem laidAt_of_matrixOk {a : ReqArray} {R T : ℕ} (h : laidMatrixOk a R T = true) {i c : ℕ}
    (hi : i < a.sizeI) (hc : c < a.sizeC) : (laidAt a i c).isSome = true := by
  simp only [laidMatrixOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hall, hno⟩, hsum⟩ := h
  have hs : (a.blocks.map fun b => 2 ^ b.bitsI * 2 ^ b.bitsC).sum = a.sizeI * a.sizeC := by
    rw [← hsum, List.sum_eq_foldl]
    simp only [pow_add]
  obtain ⟨b, hb, hh⟩ := cover_all a.blocks a.sizeI a.sizeC
    (fun b hb => ⟨(hall b hb).1.2, (hall b hb).2⟩)
    ((pairwise_of_noPair meetB a.blocks hno).imp fun k => disjoint_of_meetB k) hs hi hc
  exact laidAt_of_holds hb hh

/-- The test on one message's arrays holds the test on each matrix. -/
theorem matrix_of_message {codes : Codes} {o : OracleShape} {inIt : List ReqArray}
    (h : reqMessageLayoutOk codes o inIt = true) {A : ReqArray} (hA : A ∈ inIt) :
    laidMatrixOk A (ceilLog2 o.mainRows) (codes.base.getD o.code default).logEll = true := by
  unfold reqMessageLayoutOk at h
  have hne : inIt.isEmpty = false := by
    cases inIt with
    | nil => cases hA
    | cons _ _ => rfl
  rw [hne, Bool.false_or, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  split at h
  · rename_i c pad hc hp
    simp only [Bool.and_eq_true, laidOk, List.all_eq_true] at h
    have e : codes.base.getD o.code default = c := by
      simp [Array.getD_eq_getD_getElem?, hc]
    rw [e]
    exact h.1.1 A hA
  · cases h

/-- **The covering under the test on a layout.** -/
theorem laidAt_of_layout {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (h : reqLayoutOk codes shape layout = true) {l : ℕ} {as : List ReqArray}
    (hl : layout.link[l]? = some as) {A : ReqArray} (hA : A ∈ as) {i c : ℕ} (hi : i < A.sizeI)
    (hc : c < A.sizeC) : (laidAt A i c).isSome = true := by
  obtain ⟨m, -, hM⟩ := message_of_layout h hl hA
  exact laidAt_of_matrixOk (matrix_of_message hM
    (List.mem_filter.2 ⟨hA, beq_self_eq_true _⟩ : A ∈ as.filter fun a => a.message == A.message))
    hi hc

/-! ## The test laidThere without its walk over the elements -/

/-- **A test on public letters alone**: for every entry of the 25 lists the array that its label
names is there in the layout and has the entry's rows of symbols and columns. -/
def namedThere (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) : Bool :=
  (List.range 25).all fun k => (List.range (s k).NM).all fun a =>
    match arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
    | none => false
    | some A => A.sizeI == Alg.symRows ((s k).m a) && A.sizeC == (s k).k a

/-- **Under the test on the layout that test gives laidThere.** -/
theorem laidThere_of_named {codes : Codes} {shape : ReqShape} {layout : ReqLayout}
    (h : reqLayoutOk codes shape layout = true) {X : Model.Verify.Public} {s : ℕ → Size}
    (T : namedThere X s layout = true) : laidThere X s layout = true := by
  unfold namedThere at T
  unfold laidThere
  rw [List.all_eq_true] at T ⊢
  intro k hk
  have T1 := T k hk
  rw [List.all_eq_true] at T1 ⊢
  intro a ha
  have T2 := T1 a ha
  cases hA : arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
  | none =>
    simp only [hA] at T2
    cases T2
  | some A =>
    simp only [hA] at T2 ⊢
    obtain ⟨as, hl, hf⟩ := Option.bind_eq_some_iff.1 hA
    rw [Bool.and_eq_true]
    refine ⟨T2, ?_⟩
    rw [List.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro c hc
    exact laidAt_of_layout h hl (List.mem_of_find?_eq_some hf) (List.mem_range.1 hi)
      (List.mem_range.1 hc)

end Meaning

#print axioms Meaning.laidAt_of_holds
#print axioms Meaning.laidAt_of_matrixOk
#print axioms Meaning.matrix_of_message
#print axioms Meaning.laidAt_of_layout
#print axioms Meaning.laidThere_of_named
