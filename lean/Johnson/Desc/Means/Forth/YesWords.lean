--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Forth/YesWords.lean: when the test "all three words of a row's coefficient are 0"
is passed.

Before a row is added to a group, the IOP as written in Lean asks that the row has no coefficient on
an entry that masks an answer to an out-of-domain (OOD) sample. The test compares machine words with
0 (Johnson/Desc/Own/Rows.lean: allZero). Laws on rows speak of what a coefficient reads as in the
field. This file joins the two: a row's coefficient is a sum that the program's addition has made,
so its words are below the prime, and on such words "all words are 0" and "reads as 0" are the same.

Main names:
  okE_sum             the words of a sum are below the prime, whatever the summands' words are
  okE_foldl           so are those of a sum that a loop adds up, if it starts from such words
  okE_coefficient     so are those of a row's coefficient on an entry
  allZero_of_val      on words below the prime: reads as 0 in the library's field, so all words
                      are 0
  allZero_coefficient **a coefficient that reads as 0 passes the test on words**

What is not claimed. Nothing on which rows have such a coefficient. Nothing on soundness, on
completeness or on hiding.

-/
import OnBytes.Slice.ProgField
import OnBytes.Slice.SimBase
import OnBytes.Model.HideLaws
import OnBytes.Iop.Ground
import Johnson.Desc.Own.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- The three words of a sum in the extension field are below the prime. -/
theorem okE_sum (a b : E) : okE (addE a b) = true := by
  rw [okE_triple, addE_triple]
  exact Slice.okE_addE _ _

/-- A sum that a loop adds up, from words below the prime on, has words below the prime. -/
theorem okE_foldl {α : Type} (l : List α) (cond : α → Bool) (val : α → E) (a : E)
    (ha : okE a = true) :
    okE (l.foldl (fun s t => if cond t then addE s (val t) else s) a) = true := by
  induction l generalizing a with
  | nil => exact ha
  | cons t l ih =>
    rw [List.foldl_cons]
    by_cases h : cond t = true
    · rw [if_pos h]
      exact ih _ (okE_sum _ _)
    · rw [if_neg h]
      exact ih _ ha

/-- The words of a row's coefficient on an entry are below the prime. -/
theorem okE_coefficient (r : Row) (o : Nat) (part : Part) (idx : Nat) :
    okE (r.coefficient o part idx) = true := by
  unfold Row.coefficient
  simp only [← Array.foldl_toList]
  exact okE_foldl _ _ _ _ (okE_foldl _ _ _ _ (okE_foldl _ _ _ _ (okE_foldl _ _ _ _ rfl)))

/-- On words below the prime: an element that reads as 0 in the library's field has the words 0. -/
theorem allZero_of_val (x : E) (hx : okE x = true) (h : Model.Reading.gl.val x = 0) :
    VerifiableInference.Desc.Own.allZero x = true := by
  have h' : Slice.readE x = 0 := h
  exact (Slice.isZeroE_iff x hx).2 h'

/-- **A coefficient that reads as 0 passes the test on words.** -/
theorem allZero_coefficient (r : Row) (o : Nat) (part : Part) (idx : Nat)
    (h : Model.Reading.gl.val (r.coefficient o part idx) = 0) :
    VerifiableInference.Desc.Own.allZero (r.coefficient o part idx) = true :=
  allZero_of_val _ (okE_coefficient r o part idx) h

end OnBytes.Means

#print axioms OnBytes.Means.okE_sum
#print axioms OnBytes.Means.okE_foldl
#print axioms OnBytes.Means.okE_coefficient
#print axioms OnBytes.Means.allZero_of_val
#print axioms OnBytes.Means.allZero_coefficient
