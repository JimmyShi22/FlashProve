-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/FoldShift.lean: any change of the 2 k + 1 values of a hiding polynomial's k rounds
is a change of its coefficients, in the library's own names for the coefficients.
Definitions, statements and proofs. Pure algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  fold_shift    For all coefficients W, every carried value A (see Johnson/LinkSim/FoldTriTie.lean)
                and every point g, if dr has k pairs: with W + shiftH k ds dr in place of W, the
                sum (hMu) changes by ds, and the rounds' coefficients 0 and 2 (pairsOf of hTr)
                change by dr.
Here shiftH k ds dr is the coefficient change unW ds dr of Johnson/LinkSim/FoldTri.lean, written in
the library's names (ofList).

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean). It is shown_shiftW
(Johnson/LinkSim/FoldTri.lean) carried over by hMu_list and hTr_list
(Johnson/LinkSim/FoldTriTie.lean). Johnson/LinkSim/AtText/Fold.lean uses it.

Other names (namespace OnBytes.LinkSim).
  ofList k l c   from a list of pairs and a constant back to coefficients under the library's names
                 (HIdx (sVars E 2 k)); 0 where the list is too short.
  listW_ofList   listW after ofList gives back the list and the constant, if the list has k pairs.
  listW_add      listW is additive.
  length_listW   listW gives k pairs.

Limits. As in Johnson/LinkSim/FoldTriTie.lean: the rounds' linear coefficients are not spoken of.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.FoldTriTie

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb

variable {E : Type} [Field E]

/-- From a list of pairs and a constant back to coefficients under the library's names; 0 where the
list is too short. -/
def ofList : (k : ℕ) → List (E × E) → E → HIdx (sVars E 2 k) → E
  | 0, _, c => fun _ => c
  | k + 1, l, c => fun i =>
    match i with
    | .inl t => if t = (0 : Fin 2) then (l.headD (0, 0)).1 else (l.headD (0, 0)).2
    | .inr j => ofList k l.tail c j

/-- listW gives one pair per variable. -/
theorem length_listW : ∀ (k : ℕ) (W : HIdx (sVars E 2 k) → E), (listW k W).1.length = k
  | 0, _ => rfl
  | k + 1, W => congrArg (· + 1) (length_listW k fun i => W (.inr i))

/-- listW after ofList gives back the list and the constant, if the list has k pairs. -/
theorem listW_ofList : ∀ (k : ℕ) (l : List (E × E)) (c : E), l.length = k →
    listW k (ofList k l c) = (l, c)
  | 0, [], _, _ => rfl
  | 0, _ :: _, _, h => by cases h
  | _ + 1, [], _, h => by cases h
  | k + 1, x :: l, c, h => by
      show ((x.1, x.2) :: (listW k (ofList k l c)).1, (listW k (ofList k l c)).2) = (x :: l, c)
      rw [listW_ofList k l c (Nat.succ.inj h)]

/-- listW is additive. -/
theorem listW_add : ∀ (k : ℕ) (W W' : HIdx (sVars E 2 k) → E),
    listW k (W + W') = (addW (listW k W).1 (listW k W').1, (listW k W).2 + (listW k W').2)
  | 0, _, _ => rfl
  | k + 1, W, W' => by
      show ((W _ + W' _, W _ + W' _) ::
          (listW k ((fun i => W (.inr i)) + fun i => W' (.inr i))).1,
        (listW k ((fun i => W (.inr i)) + fun i => W' (.inr i))).2) = _
      rw [listW_add k (fun i => W (.inr i)) fun i => W' (.inr i)]
      rfl

/-- The change of the coefficients, unW ds dr in the library's names. -/
def shiftH (k : ℕ) (ds : E) (dr : List (E × E)) : HIdx (sVars E 2 k) → E :=
  ofList k (unW ds dr).1 (unW ds dr).2

/-- Adding shiftH k ds dr to the coefficients changes the sum by ds and the rounds' coefficients 0
and 2 by dr, for every A and g, if dr has k pairs. -/
theorem fold_shift (k : ℕ) (W : HIdx (sVars E 2 k) → E) (ds : E) (dr : List (E × E))
    (h : dr.length = k) (A : E) (g : HPt (sVars E 2 k)) :
    hMu (sVars E 2 k) (W + shiftH k ds dr) = hMu (sVars E 2 k) W + ds ∧
      pairsOf k (hTr (sVars E 2 k) A (W + shiftH k ds dr) g) =
        addW (pairsOf k (hTr (sVars E 2 k) A W g)) dr := by
  have e : listW k (W + shiftH k ds dr) =
      shiftW (listW k W).1 (listW k W).2 ds dr := by
    rw [listW_add, shiftH, listW_ofList k _ _ (by rw [length_unW, h])]
    rfl
  have hs := shown_shiftW (listW k W).1 (listW k W).2 ds dr (by rw [length_listW, h])
  rw [hMu_list, hTr_list, hMu_list, hTr_list, e]
  exact hs

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.listW_ofList
#print axioms OnBytes.LinkSim.fold_shift
