-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormPads.lean: THE FORM's HALF: NO COEFFICIENT BEYOND A ROW's WRITTEN SUPPORT:
the three words of a row's coefficient are 0 wherever the coefficient reads as 0 in the field; and a
vector that is cut below a length and laid on a table reads as 0 from that length on.

Why. The tests of a new open row (Ground.rowL, Johnson/Desc/First/Base/Ground.lean) ask that a row
has the coefficient 0, AS WORDS, on certain public places of its group's members. The library's laws
on rows speak of what a coefficient READS AS in a field. This file is the bridge.

Main names.
  Beyond lay N i    the index i lies inside the table, and the vector's entry that stands there has
    a number from N on.
  foldl_okE, okE_coefficient   a row's coefficient has words below the prime, at every row: it is 0
    or the output of a sum.
  isZero_of_val     so: if it reads as 0 in the library's field, its three words are 0.
  laid_cut_zero     a vector cut below a length and laid on a table.

Limits. Nothing on a row of a given protocol: Johnson/Prover/Link/FormPadsRows.lean. Vectors with a
written-out factor are not served by laid_cut_zero.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K14.Law.MeansLoc
import Johnson.Desc.K14.Law.MeansRec
import Johnson.Desc.Kinds.Law.Lemma2a
import OnBytes.Slice.ProgField
import OnBytes.Slice.BlkForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open OnBytes.Model (Reading)

/-- The index i of a table lies inside the table, and the vector's entry that stands there has a
number from N on. -/
def Beyond (lay : VectorLay) (N i : Nat) : Prop := i < 2 ^ lay.bits ∧ N ≤ lay.entryAt i

/-- A sum that takes some summands and passes over the others keeps its words below the prime. -/
theorem foldl_okE {α : Type} (c : α → Prop) [∀ a, Decidable (c a)] (f : α → E) :
    ∀ (l : List α) (s : E), okE s = true →
      okE (l.foldl (fun s a => if c a then addE s (f a) else s) s) = true
  | [], _, hs => hs
  | a :: l, s, hs => by
    rw [List.foldl_cons]
    refine foldl_okE c f l _ ?_
    by_cases h : c a
    · rw [if_pos h]
      exact VerifiableInference.Desc.Kinds.Head.Law.okE_addE _ _
    · rw [if_neg h]
      exact hs

/-- **A row's coefficient has words below the prime.** -/
theorem okE_coefficient (r : Row) (o : Nat) (pt : Part) (i : Nat) :
    okE (r.coefficient o pt i) = true := by
  unfold Row.coefficient
  simp only [← Array.foldl_toList]
  exact foldl_okE _ _ _ _ (foldl_okE _ _ _ _ (foldl_okE _ _ _ _ (foldl_okE _ _ _ _ rfl)))

/-- **If a row's coefficient reads as 0 in the field, its three words are 0.** -/
theorem isZero_of_val (r : Row) (o : Nat) (pt : Part) (i : Nat)
    (h : Reading.gl.val (r.coefficient o pt i) = 0) : isZeroE (r.coefficient o pt i) = true :=
  (Slice.isZeroE_iff _ (okE_coefficient r o pt i)).2 h

/-- **A vector cut below a length and laid on a table reads as 0 from that length on.** -/
theorem laid_cut_zero {K : Type} [Field K] (ρ : Reading K) (lay : VectorLay) (v : Tensor)
    (count len : Nat) (L : List Tensor) (i : Nat) (hd : v.denseVars = []) (hv : v.vars = count)
    (hb : count ≤ lay.bits) (hL : tensorBelow v 0 count len = some L) (hi : Beyond lay len i) :
    (L.map fun t => ρ.val ((lay.onTable t).entry i)).sum = 0 := by
  have hmem := Desc.K14.Law.tensorBelow_mem v hd 0 count len L hL
  have e : (L.map fun t => ρ.val ((lay.onTable t).entry i)) =
      L.map fun t => if lay.entryAt i < 2 ^ count then ρ.val (t.entry (lay.entryAt i)) else 0 :=
    List.map_congr_left fun t ht => by
      rw [Slice.entry_onTable ρ lay t (hmem t ht).1 (by rw [(hmem t ht).2, hv]; exact hb) i hi.1,
        (hmem t ht).2, hv]
  rw [e]
  by_cases hj : lay.entryAt i < 2 ^ count
  · simp only [hj, if_true]
    rw [Desc.K14.Law.tensorBelow_val ρ v hd 0 count len L hL, if_neg]
    rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hj]
    exact Nat.not_lt.2 hi.2
  · simp [hj]

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.foldl_okE
#print axioms Johnson.Prover.Link.okE_coefficient
#print axioms Johnson.Prover.Link.isZero_of_val
#print axioms Johnson.Prover.Link.laid_cut_zero
