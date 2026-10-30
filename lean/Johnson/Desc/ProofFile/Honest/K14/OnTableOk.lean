-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OnTableOk.lean: A VECTOR OF PRODUCT FORM THAT PASSES THE PROGRAM's
TEST ON A VECTOR (Tensor.ok, OnBytes/Iop/Tensor.lean) STILL PASSES IT WHEN IT IS LAID ON A TABLE
(VectorLay.onTable, the same file): ALSO WHERE IT HAS WRITTEN-OUT VARIABLES (the library's word:
dense). Statements with their proofs. No definition. General in the layout and the vector; it stands
over the library alone.

Why. The library has this where no variable is written out (onTable_vars,
OnBytes/Slice/BlkLinRead.lean; laid_term_fits, Johnson/Desc/K14/Honest/YesCut.lean; laid_term,
Johnson/Prover/Link/FormRowsLaws.lean) and at the vector eq(psi) (inOrder_onTable,
Johnson/Desc/K13/Honest/RowsAccept.lean); at written-out variables it has a test at three vectors
(OnBytes/Iop/TestTensor.lean), no law. The weights of the row (Dot) have written-out variables.

  padded_inOrder  the first step of onTable: filled up at the top, by variables that pick the bit 0,
                  to the table's number of variables: by the library's inOrder_insertChoice
                  (OnBytes/Slice/BlkProxOrder.lean)
  turned_inOrder  the second step, where the rows' bits are the high ones: the variables are turned
                  by the number of a place's bits and the written-out variables renumbered: each
                  still has the pair (1, 1), and none is named twice
  onTable_inOrder **the two together**, in the proposition InOrder of
                  Johnson/Desc/Own/ShapesMean.lean; and the laid vector has the table's number of
                  variables
  onTable_tensorInOrder, onTable_ok   **the same of the description's own test**
                  (Own.tensorInOrder) **and of the program's** (Tensor.ok), by the library's
                  tensorInOrder_iff and tensorInOrder_agrees

THE PREMISES: the vector passes the test; it has at most as many variables as the table; the table
has at most 63.

What is not claimed. Nothing on the laid vector's entries (the library's onTable_entryG,
Johnson/Desc/K14/Law/LayDense.lean, is on these). Nothing on any property.
-/
import Johnson.Desc.Own.ShapesMean
import Johnson.Desc.Own.ShapesAgree
import OnBytes.Slice.BlkProxOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes
open VerifiableInference.Desc.Own (InOrder tensorInOrder tensorInOrder_iff tensorInOrder_agrees)

/-- A vector in order, filled up at the top to n variables by variables that pick the bit 0, is in
order and has n variables. -/
theorem padded_inOrder (v : Tensor) (n : Nat) (h : InOrder v) (hb : v.vars ≤ n) (h63 : n ≤ 63) :
    InOrder (v.insertChoice v.vars (n - v.vars) 0) ∧
      (v.insertChoice v.vars (n - v.vars) 0).pairs.length = n := by
  obtain ⟨_, h2, h3, h4⟩ := h
  have hv : v.vars = v.pairs.length := rfl
  have hO := OnBytes.Slice.ProxRun.inOrder_insertChoice (v := v) ⟨h4, h3⟩ v.vars (n - v.vars) 0
  have hl : (v.insertChoice v.vars (n - v.vars) 0).pairs.length = n := by
    show (v.pairs.take v.vars ++ choicePairs (n - v.vars) 0 ++ v.pairs.drop v.vars).length = n
    rw [List.length_append, List.length_append, List.length_take, List.length_drop,
      OnBytes.Slice.ProxRun.length_choicePairs]
    omega
  refine ⟨⟨by rw [hl]; exact h63, ?_, hO.2, hO.1⟩, hl⟩
  show (v.denseVars.map fun d => if v.vars ≤ d then d + (n - v.vars) else d) = [] ∨
    v.first + 2 ^ (v.denseVars.map fun d => if v.vars ≤ d then d + (n - v.vars) else d).length ≤
      v.values.size
  rcases h2 with h2 | h2
  · left
    rw [h2]
    rfl
  · right
    rw [List.length_map]
    exact h2

/-- A vector in order of rB + pB variables, turned by pB variables with its written-out variables
renumbered, is in order and has as many variables. -/
theorem turned_inOrder (w : Tensor) (rB pB : Nat) (h : InOrder w)
    (hl : w.pairs.length = rB + pB) :
    InOrder { w.rotate pB with
        denseVars := w.denseVars.map fun d => if pB ≤ d then d - pB else d + rB } ∧
      ({ w.rotate pB with
        denseVars := w.denseVars.map fun d => if pB ≤ d then d - pB else d + rB } :
          Tensor).pairs.length = rB + pB := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlt : ∀ d ∈ w.denseVars, d < rB + pB := fun d hd => by
    rw [← hl]
    exact (List.getElem?_eq_some_iff.1 (h3 d hd)).1
  have hlen : (w.pairs.drop pB ++ w.pairs.take pB).length = rB + pB := by
    rw [List.length_append, List.length_drop, List.length_take]
    omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hlen⟩
  · show (w.pairs.drop pB ++ w.pairs.take pB).length ≤ 63
    rw [hlen, ← hl]
    exact h1
  · show (w.denseVars.map fun d => if pB ≤ d then d - pB else d + rB) = [] ∨
      w.first + 2 ^ (w.denseVars.map fun d => if pB ≤ d then d - pB else d + rB).length ≤
        w.values.size
    rcases h2 with h2 | h2
    · left
      rw [h2]
      rfl
    · right
      rw [List.length_map]
      exact h2
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hd'
    have hp := h3 d hd
    have hd2 := hlt d hd
    show (w.pairs.drop pB ++ w.pairs.take pB)[if pB ≤ d then d - pB else d + rB]? = _
    have hdl : (w.pairs.drop pB).length = rB := by
      rw [List.length_drop]
      omega
    by_cases hc : pB ≤ d
    · rw [if_pos hc, List.getElem?_append_left (by rw [hdl]; omega), List.getElem?_drop, ← hp]
      congr 1
      omega
    · rw [if_neg hc, List.getElem?_append_right (by rw [hdl]; omega), hdl,
        List.getElem?_take_of_lt (by omega), ← hp]
      congr 1
      omega
  · show (w.denseVars.map fun d => if pB ≤ d then d - pB else d + rB).Nodup
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) h4
    have ha2 := hlt a ha
    have hb2 := hlt b hb
    split at hab <;> split at hab <;> omega

/-- **A vector in order, laid on a table of at most 63 variables and of no fewer than its own, is in
order and has the table's number of variables**: also where it has written-out variables. -/
theorem onTable_inOrder (lay : VectorLay) (v : Tensor) (h : InOrder v) (hb : v.vars ≤ lay.bits)
    (h63 : lay.bits ≤ 63) :
    InOrder (lay.onTable v) ∧ (lay.onTable v).vars = lay.bits := by
  obtain ⟨a, b⟩ := padded_inOrder v lay.bits h hb h63
  unfold VectorLay.onTable
  dsimp only
  split
  · exact turned_inOrder _ lay.rowBits lay.placeBits a b
  · exact ⟨a, b⟩

/-- The same of the description's own test. -/
theorem onTable_tensorInOrder (lay : VectorLay) (v : Tensor) (h : tensorInOrder v = true)
    (hb : v.vars ≤ lay.bits) (h63 : lay.bits ≤ 63) :
    tensorInOrder (lay.onTable v) = true ∧ (lay.onTable v).vars = lay.bits := by
  obtain ⟨a, b⟩ := onTable_inOrder lay v ((tensorInOrder_iff v).1 h) hb h63
  exact ⟨(tensorInOrder_iff _).2 a, b⟩

/-- The same of the program's test. -/
theorem onTable_ok (lay : VectorLay) (v : Tensor) (h : v.ok = true) (hb : v.vars ≤ lay.bits)
    (h63 : lay.bits ≤ 63) : (lay.onTable v).ok = true ∧ (lay.onTable v).vars = lay.bits := by
  rw [tensorInOrder_agrees] at h ⊢
  exact onTable_tensorInOrder lay v h hb h63

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.padded_inOrder
#print axioms ProofFile.Honest.K14.turned_inOrder
#print axioms ProofFile.Honest.K14.onTable_inOrder
#print axioms ProofFile.Honest.K14.onTable_tensorInOrder
#print axioms ProofFile.Honest.K14.onTable_ok
