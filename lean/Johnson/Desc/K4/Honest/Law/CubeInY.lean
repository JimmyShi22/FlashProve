-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/CubeInY.lean: CONDITIONAL. Statements with their proofs; no definition.

What is here. `polyInY` (Johnson/Desc/K4/Honest/Cube.lean) returns the coefficients of Y ↦ f (ends +
Y masks), where that function, read in the library's extension field, is a polynomial of degree at
most dY.

  `PolyOn.const`, `.entry`, `.entryA`, `.head`, `.mono`, `.add`, `.mul`, `.foldl` functions that
  read as polynomials
  `gl_getD_map`; `ReadsAlike.const`, `.entry`, `.entryA`, `.head`, `.add`, `.mul`, `.foldl`
  functions that read alike on lists that read alike
  `maskedEnds_zero`, `maskedEnds_read`   the masked end values, read
  `polyInY_length`   dY + 1 coefficients, where the two lists are equally long
  `polyInY_poly`   **the law**: the list, as a polynomial, is P
  `polyInY_coeff`, `polyInY_eval`   its coefficients and its values are P's
  `polyInY_value`, `polyInY_const`   under `PolyOn`: its value at y, and its constant coefficient
  `polyInY_const'`   under `ReadsAlike` too: the constant coefficient is f on the end values

Limits. At the reading `Reading.gl` alone. THAT f IS SUCH A POLYNOMIAL IS A HYPOTHESIS (`PolyOn`, or
a polynomial P that meets f at Y = 0, .., dY): it is owed for each function anew; the lemmas of
section 1 build it for a function that is written with the program's sums, products and loops over
lists. THAT THERE ARE AS MANY MASK ENTRIES AS END VALUES IS A HYPOTHESIS too: where the two lengths
differ `polyInY` returns the empty list. The degree is below 2 ^ 32 - 1. The constant coefficient is
tied to f at `maskedEnds ends masks zeroE`; these values read as the end values (`maskedEnds_zero`);
to f at the end values themselves it is tied under the hypothesis `ReadsAlike f` (`polyInY_const'`),
which is owed for each function anew as well.

Kin. `gl_getD_map` is `getD_mapL` (Johnson/Desc/K4/Honest/Law/CubeKitB.lean) at the reading
`Reading.gl`. This file does not build on it. `maskedEnds_zero` is `maskedEnds_zero_aux`
(Johnson/Desc/K4/Honest/Law/CubeKitY.lean) under the name by which it is called: one statement.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.CubeKitY

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes (E addE subE mulE negE invE maddE ofF zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (polyOf)
open Polynomial

/-! ## 1 Functions that read as polynomials -/

/-- A function that does not read its argument. -/
theorem PolyOn.const (a : E) : PolyOn 0 fun _ => a :=
  ⟨C (Reading.gl.val a), by simp, fun _ => by simp⟩

/-- An entry of the masked end values has degree at most 1. -/
theorem PolyOn.entry (ends masks : List E) (i : ℕ) :
    PolyOn 1 fun y => (maskedEnds ends masks y).getD i zeroE := by
  have e : ∀ y, (maskedEnds ends masks y).getD i zeroE =
      (((ends.zip masks)[i]?).map fun x => addE x.1 (mulE y x.2)).getD zeroE := by
    intro y
    simp [maskedEnds, List.getD_eq_getElem?_getD]
  cases h : (ends.zip masks)[i]? with
  | none =>
    refine ⟨0, by simp, fun y => ?_⟩
    show Reading.gl.val ((maskedEnds ends masks y).getD i zeroE) = _
    rw [e, h]
    simp [Reading.gl.zero]
  | some x =>
    refine ⟨C (Reading.gl.val x.2) * X + C (Reading.gl.val x.1), natDegree_linear_le, fun y => ?_⟩
    show Reading.gl.val ((maskedEnds ends masks y).getD i zeroE) = _
    rw [e, h]
    simp only [Option.map_some, Option.getD_some, Reading.gl.add, Reading.gl.mul, eval_add,
      eval_mul, eval_C, eval_X]
    ring

/-- The same entry, where the masked end values are laid into an array. -/
theorem PolyOn.entryA (ends masks : List E) (i : ℕ) :
    PolyOn 1 fun y => (maskedEnds ends masks y).toArray.getD i zeroE := by
  have e : (fun y => (maskedEnds ends masks y).toArray.getD i zeroE) =
      fun y => (maskedEnds ends masks y).getD i zeroE := by
    funext y
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  rw [e]
  exact PolyOn.entry ends masks i

/-- The first of the masked end values. -/
theorem PolyOn.head (ends masks : List E) :
    PolyOn 1 fun y => (maskedEnds ends masks y).headD zeroE := by
  have e : (fun y => (maskedEnds ends masks y).headD zeroE) =
      fun y => (maskedEnds ends masks y).getD 0 zeroE := by
    funext y
    cases maskedEnds ends masks y <;> rfl
  rw [e]
  exact PolyOn.entry ends masks 0

/-- A higher bound on the degree. -/
theorem PolyOn.mono {d d' : ℕ} {F : E → E} (h : PolyOn d F) (hd : d ≤ d') : PolyOn d' F := by
  obtain ⟨P, hP, hv⟩ := h
  exact ⟨P, hP.trans hd, hv⟩

/-- A sum. -/
theorem PolyOn.add {d : ℕ} {F G : E → E} (hF : PolyOn d F) (hG : PolyOn d G) :
    PolyOn d fun y => addE (F y) (G y) := by
  obtain ⟨P, hP, hv⟩ := hF
  obtain ⟨Q, hQ, hw⟩ := hG
  exact ⟨P + Q, (natDegree_add_le _ _).trans (max_le hP hQ), fun y => by
    rw [Reading.gl.add, hv, hw, eval_add]⟩

/-- A product: the degrees add. -/
theorem PolyOn.mul {d d' : ℕ} {F G : E → E} (hF : PolyOn d F) (hG : PolyOn d' G) :
    PolyOn (d + d') fun y => mulE (F y) (G y) := by
  obtain ⟨P, hP, hv⟩ := hF
  obtain ⟨Q, hQ, hw⟩ := hG
  exact ⟨P * Q, natDegree_mul_le.trans (Nat.add_le_add hP hQ), fun y => by
    rw [Reading.gl.mul, hv, hw, eval_mul]⟩

/-- A loop over a list: st y is the loop's step at the argument y. -/
theorem PolyOn.foldl {α : Type} {d : ℕ} (st : E → E → α → E) : ∀ (l : List α) (F : E → E),
    PolyOn d F → (∀ a ∈ l, ∀ G : E → E, PolyOn d G → PolyOn d fun y => st y (G y) a) →
    PolyOn d fun y => l.foldl (st y) (F y)
  | [], _, hF, _ => hF
  | a :: l, F, hF, h =>
    PolyOn.foldl st l (fun y => st y (F y) a) (h a (by simp) F hF)
      fun b hb G hG => h b (by simp [hb]) G hG

/-! ## 1b Functions that read alike on lists that read alike -/

/-- An entry of the list of the readings is the reading of the entry. -/
theorem gl_getD_map : ∀ (l : List E) (i : ℕ),
    (l.map Reading.gl.val).getD i 0 = Reading.gl.val (l.getD i zeroE)
  | [], i => by simp [Reading.gl.zero]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => gl_getD_map l i

/-- A function that does not read its argument. -/
theorem ReadsAlike.const (a : E) : ReadsAlike fun _ => a := fun _ _ _ => rfl

/-- An entry of the list. -/
theorem ReadsAlike.entry (i : ℕ) : ReadsAlike fun e => e.getD i zeroE := fun a b h => by
  rw [← gl_getD_map, ← gl_getD_map, h]

/-- The same entry, where the list is laid into an array. -/
theorem ReadsAlike.entryA (i : ℕ) : ReadsAlike fun e => e.toArray.getD i zeroE := by
  have e : (fun e : List E => e.toArray.getD i zeroE) = fun e => e.getD i zeroE := by
    funext l
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  rw [e]
  exact ReadsAlike.entry i

/-- The first of the list. -/
theorem ReadsAlike.head : ReadsAlike fun e => e.headD zeroE := by
  have e : (fun e : List E => e.headD zeroE) = fun e => e.getD 0 zeroE := by
    funext l
    cases l <;> rfl
  rw [e]
  exact ReadsAlike.entry 0

/-- A sum. -/
theorem ReadsAlike.add {f g : List E → E} (hf : ReadsAlike f) (hg : ReadsAlike g) :
    ReadsAlike fun e => addE (f e) (g e) := fun a b h => by
  rw [Reading.gl.add, Reading.gl.add, hf a b h, hg a b h]

/-- A product. -/
theorem ReadsAlike.mul {f g : List E → E} (hf : ReadsAlike f) (hg : ReadsAlike g) :
    ReadsAlike fun e => mulE (f e) (g e) := fun a b h => by
  rw [Reading.gl.mul, Reading.gl.mul, hf a b h, hg a b h]

/-- A loop over a list: st e is the loop's step at the argument e. -/
theorem ReadsAlike.foldl {α : Type} (st : List E → E → α → E) : ∀ (l : List α) (f : List E → E),
    ReadsAlike f → (∀ a ∈ l, ∀ g : List E → E, ReadsAlike g → ReadsAlike fun e => st e (g e) a) →
    ReadsAlike fun e => l.foldl (st e) (f e)
  | [], _, hf, _ => hf
  | a :: l, f, hf, h =>
    ReadsAlike.foldl st l (fun e => st e (f e) a) (h a (by simp) f hf)
      fun b hb g hg => h b (by simp [hb]) g hg

/-! ## 1c The masked end values at 0 -/

/-- At Y = 0 the masked end values read as the end values. -/
theorem maskedEnds_zero (ends masks : List E) (hl : ends.length = masks.length) :
    (maskedEnds ends masks zeroE).map Reading.gl.val = ends.map Reading.gl.val :=
  maskedEnds_zero_aux ends masks hl

/-- An entry of the masked end values, read: the end value plus y times its mask entry. Beyond the
lists both sides are 0. -/
theorem maskedEnds_read : ∀ (ends masks : List E), ends.length = masks.length → ∀ (y : E) (i : ℕ),
    Reading.gl.val ((maskedEnds ends masks y).getD i zeroE) =
      Reading.gl.val (ends.getD i zeroE) + Reading.gl.val y * Reading.gl.val (masks.getD i zeroE)
  | [], [], _, y, i => by simp [maskedEnds, Reading.gl.zero]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | a :: e, b :: m, _, y, 0 => by
    show Reading.gl.val (addE a (mulE y b)) = _
    rw [Reading.gl.add, Reading.gl.mul]
    rfl
  | _ :: e, _ :: m, h, y, i + 1 => maskedEnds_read e m (by simpa using h) y i

/-! ## 2 The polynomial in Y -/

/-- dY + 1 coefficients. -/
theorem polyInY_length (dY : ℕ) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) : (polyInY dY f ends masks).length = dY + 1 := by
  rw [polyInY_eq dY f ends masks hl, fold_length _ 0 _ rfl, diffs_length]
  simp

/-- **The list that `polyInY` returns is, as a polynomial, P**: for every polynomial P of degree at
most dY whose values at 0, .., dY are the readings of f on the masked end values there. -/
theorem polyInY_poly (dY : ℕ) (hd : dY + 1 < 2 ^ 32) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) (P : Cb.Gl.E[X]) (hP : P.natDegree ≤ dY)
    (hf : ∀ k, k ≤ dY →
      Reading.gl.val (f (maskedEnds ends masks (ofF k.toUInt64))) = P.eval (k : Cb.Gl.E)) :
    polyOf Reading.gl (polyInY dY f ends masks) = P := by
  have hinv : ∀ i, i < dY → ((i : Cb.Gl.E) + 1) ≠ 0 := by
    intro i hi
    have h := Code.natCast_ne_zero_of_lt Cb.Gl.E Cb.Gl.p (n := i + 1) (Nat.succ_ne_zero i) (by
      show i + 1 < Code.pGold
      rw [Code.pGold_eq]
      omega)
    rwa [Nat.cast_succ] at h
  have hlen : ((List.range (dY + 1)).map fun k =>
      f (maskedEnds ends masks (ofF k.toUInt64))).length = dY + 1 := by simp
  rw [polyInY_eq dY f ends masks hl, fold_poly _ 0 _ (by rw [diffs_length]; omega)
    (by simp [polyOf, binomP, Reading.gl.one]),
    diffs_read Reading.gl (dY + 1) _ (fun k => P.eval (k : Cb.Gl.E)) (by rw [hlen]) (by
      intro i hi
      rw [hlen] at hi
      show _ = P.eval (i : Cb.Gl.E)
      rw [← hf i (Nat.le_of_lt_succ hi)]
      simp [List.getD_eq_getElem?_getD, hi]),
    newton_eq dY hinv P hP]
  simp [polyOf]

/-- Its coefficients are P's. -/
theorem polyInY_coeff (dY : ℕ) (hd : dY + 1 < 2 ^ 32) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) (P : Cb.Gl.E[X]) (hP : P.natDegree ≤ dY)
    (hf : ∀ k, k ≤ dY →
      Reading.gl.val (f (maskedEnds ends masks (ofF k.toUInt64))) = P.eval (k : Cb.Gl.E))
    (i : ℕ) : Reading.gl.val ((polyInY dY f ends masks).getD i zeroE) = P.coeff i := by
  rw [← polyInY_poly dY hd f ends masks hl P hP hf,
    VerifiableInference.Desc.Part.MaskedSum.polyOf_coeff]

/-- Its values are P's. -/
theorem polyInY_eval (dY : ℕ) (hd : dY + 1 < 2 ^ 32) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) (P : Cb.Gl.E[X]) (hP : P.natDegree ≤ dY)
    (hf : ∀ k, k ≤ dY →
      Reading.gl.val (f (maskedEnds ends masks (ofF k.toUInt64))) = P.eval (k : Cb.Gl.E))
    (y : E) : Reading.gl.val (valueP (polyInY dY f ends masks) y) = P.eval (Reading.gl.val y) := by
  rw [← polyInY_poly dY hd f ends masks hl P hP hf]
  exact (VerifiableInference.Desc.Part.MaskedSum.polyOf_eval Reading.gl y _).symm

/-- **At every y the list's value is f on the end values masked with y.** -/
theorem polyInY_value (dY : ℕ) (hd : dY + 1 < 2 ^ 32) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) (h : PolyOn dY fun y => f (maskedEnds ends masks y)) (y : E) :
    Reading.gl.val (valueP (polyInY dY f ends masks) y) =
      Reading.gl.val (f (maskedEnds ends masks y)) := by
  obtain ⟨P, hP, hv⟩ := h
  rw [polyInY_eval dY hd f ends masks hl P hP (fun k hk => by
    rw [hv, OnBytes.Road.Hd.gl_nat (by omega)]) y, hv]

/-- The constant coefficient is f on the end values masked with 0. -/
theorem polyInY_const (dY : ℕ) (hd : dY + 1 < 2 ^ 32) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) (h : PolyOn dY fun y => f (maskedEnds ends masks y)) :
    Reading.gl.val ((polyInY dY f ends masks).getD 0 zeroE) =
      Reading.gl.val (f (maskedEnds ends masks zeroE)) := by
  obtain ⟨P, hP, hv⟩ := h
  rw [polyInY_coeff dY hd f ends masks hl P hP (fun k hk => by
    rw [hv, OnBytes.Road.Hd.gl_nat (by omega)]) 0, hv, Reading.gl.zero, coeff_zero_eq_eval_zero]

/-- **The constant coefficient is f on the end values**, where f reads alike on lists that read
alike. -/
theorem polyInY_const' (dY : ℕ) (hd : dY + 1 < 2 ^ 32) (f : List E → E) (ends masks : List E)
    (hl : ends.length = masks.length) (h : PolyOn dY fun y => f (maskedEnds ends masks y))
    (hA : ReadsAlike f) :
    Reading.gl.val ((polyInY dY f ends masks).getD 0 zeroE) = Reading.gl.val (f ends) := by
  rw [polyInY_const dY hd f ends masks hl h]
  exact hA _ _ (maskedEnds_zero ends masks hl)

end OnBytes.Desc.First.K4.Honest.CubeLaw

#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.const
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.entry
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.entryA
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.head
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.mono
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.add
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.mul
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.PolyOn.foldl
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.gl_getD_map
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.const
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.entry
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.entryA
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.head
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.add
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.mul
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.ReadsAlike.foldl
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.maskedEnds_zero
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.maskedEnds_read
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_length
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_poly
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_coeff
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_eval
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_value
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_const
#print axioms OnBytes.Desc.First.K4.Honest.CubeLaw.polyInY_const'
