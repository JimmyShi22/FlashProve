-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/AgainVals.lean: THE SMALLNESS TEST: THE FUNCTIONS IN WHICH THE VERIFIER's
SECOND COMPUTATION OF THE TIES' WEIGHTS IS WRITTEN (powersAgain, firstAgain, sumAgain, scaleE,
scaleNat: OnBytes/Model/Tail.lean, OnBytes/Model/Frame.lean), BY VALUE AND AS WORDS BELOW THE PRIME.
Lemmas; none of the library's goals. On field words, arrays and plain data: no ledger, no block, no
prover; nothing on completeness, soundness or hiding.

  `scaleE_mul`, `okE_scale`, `okE_scaleNat`, `powersAgain_ok`, `sumAgain_ok`   a product with an
      element of the base field is a product in E, as words; so these functions' outputs are words
      below the prime
  `again_step`, **`sumAgain_val`**, `sumAgain_col`   the second computation's sum over a column of
      the drawn matrix, by its value, WHERE THE COLUMN's ENTRIES ARE 1, -1 OR 0: the right side of
      foldColumn_val (OnBytes/Tie/Pv/Tail/EndLoopsB.lean). At another entry the two part: the first
      computation goes by the entry's sign, the second by its value
  **`firstAgain_eq`**   the index of a matrix's first equation, computed again, is firstOf
      (EndLoopsB.lean), where tau and each (m + 2) / 3 are at most 2^64 and the shapes' numbers of
      rows of symbols are (m + 2) / 3
By: Part.MaskedSum.okE_add, okE_sub, okE_mul (Johnson/Top/H/P1Tie/Words.lean) · pow2Again_eq,
pow2Again_tau (OnBytes/Tie/Pv/Tail/EndTested.lean) · firstOf_succ (EndIndex.lean) · the step inside
scaleE_val's proof (OnBytes/Iop/RowLaws.lean).
Limits. That a drawn matrix's entries are 1, -1 or 0 is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H.P1Tie.Words
import OnBytes.Tie.Pv.Tail.EndTested
import OnBytes.Tie.Pv.Tail.EndIndex
import OnBytes.Iop.RowLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (signOf firstOf firstOf_succ pow2Again_eq pow2Again_tau
  getD_map_range)

/-- A product with an element of the base field is the product with it as an element of E, as
words. -/
theorem scaleE_mul (s : F) (a : E) : scaleE s a = mulE (ofF s) a := by
  apply triple_inj
  rw [scaleE_triple, mulE_triple, ofF_triple, Fmt.mulE_ofF]

theorem okE_scale (s : F) (a : E) : OnBytes.okE (scaleE s a) = true := by
  rw [scaleE_mul]
  exact Part.MaskedSum.okE_mul _ _

theorem okE_scaleNat (x : E) (v : Nat) : OnBytes.okE (scaleNat x v) = true := okE_scale _ _

/-- Each of the powers of the second computation is a word below the prime. -/
theorem powersAgain_ok (theta : E) (np2 count R : Nat) (h : R < count) :
    OnBytes.okE ((powersAgain theta np2 count).getD R zeroE) = true := by
  unfold HTailF2.powersAgain
  simp only []
  rw [getD_map_range _ _ _ _ h]
  exact Part.MaskedSum.okE_mul _ _

/-- The second computation's sum over a column stays a word below the prime. -/
theorem sumAgain_ok (cf : Array Int) (base : Nat) (xi : Array E) :
    ∀ (count u : Nat) (s : E), OnBytes.okE s = true →
      OnBytes.okE (sumAgain cf base xi count u s) = true
  | 0, _, _, h => h
  | c + 1, u, s, h => by
    unfold HTailF2.sumAgain
    dsimp only
    refine sumAgain_ok cf base xi c (u + 1) _ ?_
    split
    · exact Part.MaskedSum.okE_add _ _
    · split
      · exact Part.MaskedSum.okE_sub _ _
      · exact h

/-- One step of that sum, at an entry that is 1, -1 or 0. -/
theorem again_step (x : Int) (hx : x = 1 ∨ x = -1 ∨ x = 0) (s y : E) :
    Reading.gl.val (if x == 1 then addE s y else if x == -1 then subE s y else s) =
      Reading.gl.val s + signOf (K := Cb.Gl.E) x * Reading.gl.val y := by
  rcases hx with rfl | rfl | rfl
  · show Reading.gl.val (addE s y) = _
    rw [Reading.gl.add]
    simp [signOf]
  · show Reading.gl.val (subE s y) = _
    rw [Reading.gl.sub]
    simp [signOf]
    ring
  · show Reading.gl.val s = _
    simp [signOf]

/-- **The second computation's sum over a column, by its value**, where the column's entries are 1,
-1 or 0: what the first computation's has (foldColumn_val, OnBytes/Tie/Pv/Tail/EndLoopsB.lean). -/
theorem sumAgain_val (cf : Array Int) (base : Nat) (xi : Array E)
    (hT : ∀ u, cf.getD (base + u) 0 = 1 ∨ cf.getD (base + u) 0 = -1 ∨ cf.getD (base + u) 0 = 0) :
    ∀ (count u : Nat) (s : E), Reading.gl.val (sumAgain cf base xi count u s) =
      Reading.gl.val s + ∑ j ∈ Finset.range count,
        signOf (K := Cb.Gl.E) (cf.getD (base + (u + j)) 0) * Reading.gl.val (xi.getD (u + j) zeroE)
  | 0, _, _ => by
    unfold HTailF2.sumAgain
    rw [Finset.sum_range_zero, add_zero]
  | c + 1, u, s => by
    unfold HTailF2.sumAgain
    dsimp only
    rw [sumAgain_val cf base xi hT c (u + 1) _, Finset.sum_range_succ', again_step _ (hT u)]
    have e : ∀ j, u + 1 + j = u + (j + 1) := fun j => by omega
    simp only [e, Nat.add_zero]
    ring

/-- From the column's first entry, from 0: the right side of the first computation's value law. -/
theorem sumAgain_col (cf : Array Int) (base : Nat) (xi : Array E) (tau : Nat)
    (hT : ∀ u, cf.getD (base + u) 0 = 1 ∨ cf.getD (base + u) 0 = -1 ∨ cf.getD (base + u) 0 = 0) :
    Reading.gl.val (sumAgain cf base xi tau 0 zeroE) = ∑ u ∈ Finset.range tau,
      signOf (K := Cb.Gl.E) (cf.getD (base + u) 0) * Reading.gl.val (xi.getD u zeroE) := by
  rw [sumAgain_val cf base xi hT tau 0 zeroE, Reading.gl.zero, zero_add]
  exact Finset.sum_congr rfl fun u _ => by rw [Nat.zero_add]

/-- **The index of a matrix's first equation, computed again, is the first computation's.** -/
theorem firstAgain_eq (tl : HTailF2) (hτ : tl.tau ≤ 2 ^ 64) : ∀ mu : Nat,
    (∀ nu, nu < mu → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64 ∧
      (tl.shp.getD nu {}).mS = ((tl.mats.getD nu {}).m + 2) / 3) →
    tl.firstAgain mu = firstOf tl mu
  | 0, _ => by
    unfold HTailF2.firstAgain firstOf
    rfl
  | mu + 1, h => by
    have ih := firstAgain_eq tl hτ mu fun nu hnu => h nu (by omega)
    obtain ⟨b, e⟩ := h mu (by omega)
    unfold HTailF2.firstAgain at ih ⊢
    rw [List.range_succ, List.foldl_append, ih]
    show firstOf tl mu + pow2Again tl.tau * pow2Again (((tl.mats.getD mu {}).m + 2) / 3) = _
    rw [firstOf_succ, pow2Again_tau tl hτ, pow2Again_eq _ b, e]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.scaleE_mul
#print axioms VerifiableInference.Desc.First.K8.Honest.okE_scale
#print axioms VerifiableInference.Desc.First.K8.Honest.okE_scaleNat
#print axioms VerifiableInference.Desc.First.K8.Honest.powersAgain_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.sumAgain_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.again_step
#print axioms VerifiableInference.Desc.First.K8.Honest.sumAgain_val
#print axioms VerifiableInference.Desc.First.K8.Honest.sumAgain_col
#print axioms VerifiableInference.Desc.First.K8.Honest.firstAgain_eq
