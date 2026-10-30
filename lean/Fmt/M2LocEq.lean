-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2LocEq.lean: the second toy (a chain of three links), the switch between two links: the fast
sum of the draws' rows (`sumDraws`, Fmt/M2Loc.lean) equals its meaning (`sumDrawsLit`, the literal
form: every row written out, then added under its power of theta); this holds for all arguments,
under one condition on the sizes: where there is a kept row, a row has at least three places (the
pad's three).

Theorems and proofs; a few definitions to state them with. Core Lean, no Mathlib. The file uses the
notions and lemmas of Fmt/M1CsEq.lean: lists entry by entry (`at0`); entries with their words below
p (`Can`); u + w r on lists, called a step (`stepL`).
The head of Fmt/M2Dec.lean says what the second toy is. The head of Fmt/M2Loc.lean says what the
switch does, and what the carrying message, the kept row and its second sending are. A draw is a
position that the verifier has drawn; at each draw it makes three rows, or four where there is a
kept row (`drawL`). A row is a linear claim: vectors of coefficients on the tables of the carrying
message and of the second sending, with a target value (`LRow`, Fmt/M2Types.lean).

Main names (`seven` to `all_draws`: each under the hypotheses of its statement, on lengths, on words
below p and, with a kept row, 3 ≤ C.l):
  `seven`: seven pieces that are side by side, added in the order in which the rows bring them, are
    the one list added from the place 0 on.
  `draw_true`, `draw_false`: one draw, with and without a kept row: its rows, added one after the
    other, give what the fast form's one pass (`addDrawL`) gives, from a state of the right lengths
    whose entries have their words below p (`InvL`).
  `all_draws`: all draws; a drawn position without a column gives "none" in both.
  `Spec.sumDraws_eq`, `sumDraws_eq`: the title's statement.
  `Spec.sumDrawsFrom_eq`, `sumDrawsFrom_eq`: the same, under the same condition, from any start: a
    row of the right lengths (2 l entries on the carrying message; l on the second sending, or none
    without a kept row) whose entries have their words below p: `sumDrawsFrom` = `sumDrawsFromLit`.
    `sumDrawsFrom` is the form that the decision runs (`blocks`, Fmt/M2All.lean).

Why the condition: at rows of fewer than three places the three coefficients on the old pad are read
off the generator's row by index in the one form (places counted down from the end, stopping at 0)
and cut off its end in the other: they can differ. Fmt/M2Loc.lean's test on sizes (`locFits`) has
the condition.
Why `sumDraws_eq` has no condition on the inputs: as in Fmt/M1CsEq.lean. The arithmetic is on words:
a sum or a product is reduced modulo p, an input need not be. The running sums start at 0 and are
results of additions, so adding 0 changes nothing there. A row's entry "0 + x" is under a product,
which may have a factor reduced first.

Notation: p (in "words below p" and "modulo p"): the p of the field f (`Fld.p`, Fmt/Rules1.lean);
`A0`, `A1`, `T`, `TK`, `T0`, `T1`, `OP` (the fields of `Off`, Fmt/M2Loc.lean; in `seven`, natural
numbers of the same names): where the seven pieces begin, in the order told at `restOff` in that
file's head.

Limits: this file does not say that `sumDrawsLit` is what the programs (the C++ implementation that
comes with this Lean code) compute. What has been compared with their files is told in the head of
Fmt/M2Send.lean. This file says nothing on soundness, nothing on time.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Loc
import Fmt.M1CsEq

set_option autoImplicit false

namespace Fmt.M2.LocEq
open Fmt.M1 Fmt.M1.CsEq

/-! ## Lists: a step with nothing; the entries and the length of a step -/

theorem step_nil (f : Fld) (u : List E) (w : E) (h : Can f u) : stepL f u w [] = u := by
  apply ext_at0
  · rw [length_stepL]
    simp
  · intro i hi
    rw [length_stepL] at hi
    rw [at0_stepL f u w [] i hi]
    show f.addE (at0 u i) (f.mulEF w Fld.zeroE) = _
    rw [mulEF_zero, addE_zero f _ (h i)]

/-- An entry of a step u + w r at an index within u, if r is no longer than u. -/
theorem step_at (f : Fld) (u r : List E) (w : E) (hr : r.length ≤ u.length)
    (i : Nat) (hi : i < u.length) :
    at0 (stepL f u w r) i = f.addE (at0 u i) (f.mulEF w (at0 r i)) :=
  at0_stepL f u w r i (by omega)

theorem len_step (f : Fld) (u r : List E) (w : E) (hr : r.length ≤ u.length) :
    (stepL f u w r).length = u.length := by
  rw [length_stepL]
  omega

/-! ## The carrying message's table, as a list -/

def tw (l : Nat) (a b : List E) : List E := (twoRows l a.toArray b.toArray).toList

theorem length_tw (l : Nat) (a b : List E) : (tw l a b).length = 2 * l := by
  unfold tw twoRows
  simp

theorem at0_tw (l : Nat) (a b : List E) (i : Nat) (h : i < 2 * l) :
    at0 (tw l a b) i = if i % 2 = 0 then at0 a (i / 2) else at0 b (i / 2) := by
  unfold tw twoRows at0 ent
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_ofFn, dif_pos h]
  simp only [Option.getD_some, beq_iff_eq]
  split
  · rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]
  · rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]

/-- A step on the table is a step on each of its two rows, if the rows a, b have l entries and the
added rows X, Y at most l. -/
theorem tw_step (f : Fld) (l : Nat) (a b X Y : List E) (w : E) (ha : a.length = l)
    (hb : b.length = l) (hX : X.length ≤ l) (hY : Y.length ≤ l) :
    stepL f (tw l a b) w (tw l X Y) = tw l (stepL f a w X) (stepL f b w Y) := by
  apply ext_at0
  · rw [length_stepL, length_tw, length_tw, length_tw]
    omega
  · intro i hi
    rw [length_stepL, length_tw, length_tw] at hi
    have hi' : i < 2 * l := by omega
    rw [at0_stepL f _ w _ i (by rw [length_tw, length_tw]; omega), at0_tw l a b i hi',
      at0_tw l X Y i hi', at0_tw l _ _ i hi']
    split
    · rw [step_at f a X w (by omega) (i / 2) (by omega)]
    · rw [step_at f b Y w (by omega) (i / 2) (by omega)]

/-! ## Adding a list from a place on -/

/-- b added onto u from the place o on; u's length is kept -/
def addOff (f : Fld) (u : List E) (o : Nat) (b : List E) : List E :=
  u.take o ++ addPre f (u.drop o) b

theorem length_addOff (f : Fld) (u : List E) (o : Nat) (b : List E) :
    (addOff f u o b).length = u.length := by
  unfold addOff
  rw [List.length_append, length_addPre, List.length_take, List.length_drop]
  omega

theorem at0_drop (u : List E) (o i : Nat) : at0 (u.drop o) i = at0 u (o + i) := by
  unfold at0
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem at0_take (u : List E) (o i : Nat) (h : i < o) : at0 (u.take o) i = at0 u i := by
  unfold at0
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem at0_addOff_in (f : Fld) (u : List E) (o : Nat) (b : List E) (i : Nat) (hi : i < u.length)
    (h1 : o ≤ i) (h2 : i < o + b.length) :
    at0 (addOff f u o b) i = f.addE (at0 u i) (at0 b (i - o)) := by
  unfold addOff
  rw [at0_append, if_neg (by rw [List.length_take]; omega), List.length_take,
    Nat.min_eq_left (by omega), at0_addPre f _ _ _ (by rw [List.length_drop]; omega),
    if_pos (by omega), at0_drop]
  rw [show o + (i - o) = i by omega]

theorem at0_addOff_out (f : Fld) (u : List E) (o : Nat) (b : List E)
    (i : Nat) (h : i < o ∨ o + b.length ≤ i) :
    at0 (addOff f u o b) i = at0 u i := by
  by_cases hi : i < u.length
  · unfold addOff
    by_cases h1 : i < o
    · rw [at0_append, if_pos (by rw [List.length_take]; omega), at0_take u o i h1]
    · rw [at0_append, if_neg (by rw [List.length_take]; omega), List.length_take,
        Nat.min_eq_left (by omega), at0_addPre f _ _ _ (by rw [List.length_drop]; omega),
        if_neg (by omega), at0_drop]
      rw [show o + (i - o) = i by omega]
  · rw [at0_ge _ _ (by rw [length_addOff]; omega), at0_ge _ _ (by omega)]

theorem can_addOff (f : Fld) (u : List E) (o : Nat) (b : List E) (h : Can f u) :
    Can f (addOff f u o b) := by
  intro i
  by_cases hi : i < u.length ∧ o ≤ i ∧ i < o + b.length
  · rw [at0_addOff_in f u o b i hi.1 hi.2.1 hi.2.2]
    exact okE_addE f _ _
  · by_cases h2 : i < u.length
    · rw [at0_addOff_out f u o b i (by omega)]
      exact h i
    · rw [at0_ge _ _ (by rw [length_addOff]; omega)]
      exact okE_zero f

theorem addPre_off (f : Fld) (u b : List E) : addPre f u b = addOff f u 0 b := rfl

/-! ## A step with a row that is made of pieces -/

theorem length_restOf (f : Fld) (l : Nat) :
    ∀ (ps : List (Nat × List E)) (a : Array E),
      a.toList.length = l → (ps.foldl (fun a p => addV f a (layAt l p.1 p.2)) a).toList.length = l
  | [], _, h => h
  | p :: ps, a, h => by
      refine length_restOf f l ps _ ?_
      show (addL f a.toList (layAt l p.1 p.2).toList).length = l
      rw [length_addL, length_layAt, h]
      omega

theorem length_zerosE (n : Nat) : (zerosE n).toList.length = n := by
  unfold zerosE
  simp

theorem at0_zerosE (n i : Nat) : at0 (zerosE n).toList i = Fld.zeroE := by
  unfold zerosE at0
  rw [List.getD_eq_getElem?_getD, Array.toList_replicate]
  by_cases h : i < n
  · rw [List.getElem?_replicate_of_lt h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
    rfl

/-- Entry i of a piece: the list g over the base field, under the weight w, laid from the place o
on; 0 elsewhere. -/
def pc (f : Fld) (w : E) (g : List UInt64) (o i : Nat) : E :=
  if o ≤ i then at0 (sc f w g) (i - o) else Fld.zeroE

theorem mul_piece (f : Fld) (w : E) (g : List UInt64) (l o i : Nat) (h : i < l) :
    f.mulEF w (at0 (layAt l o (g.map Fld.ofF)).toList i) = pc f w g o i := by
  rw [at0_layAt l o _ i h]
  unfold pc
  split
  · exact mulEF_at0_ofF f w g _
  · exact mulEF_zero f w

theorem at0_rest1 (f : Fld) (l o : Nat) (v : List E) (i : Nat) (h : i < l) :
    at0 (restOf f l [(o, v)]).toList i = f.addE Fld.zeroE (at0 (layAt l o v).toList i) := by
  show at0 (addL f (zerosE l).toList (layAt l o v).toList) i = _
  rw [at0_addL f _ _ i (by rw [length_zerosE, length_layAt]; omega), at0_zerosE]

theorem at0_rest2 (f : Fld) (l o o' : Nat) (v v' : List E) (i : Nat) (h : i < l) :
    at0 (restOf f l [(o, v), (o', v')]).toList i =
      f.addE (f.addE Fld.zeroE (at0 (layAt l o v).toList i)) (at0 (layAt l o' v').toList i) := by
  show at0 (addL f (addL f (zerosE l).toList (layAt l o v).toList) (layAt l o' v').toList) i = _
  rw [at0_addL f _ _ i (by rw [length_addL, length_zerosE, length_layAt, length_layAt]; omega),
    at0_addL f _ _ i (by rw [length_zerosE, length_layAt]; omega), at0_zerosE]

theorem len_rest (f : Fld) (l : Nat) (ps : List (Nat × List E)) :
    (restOf f l ps).toList.length = l :=
  length_restOf f l ps _ (length_zerosE l)

/-- A step with a row of one piece, onto a list u of l entries that have their words below p. -/
theorem step_rest1 (f : Fld) (l : Nat) (u : List E) (hu : u.length = l) (hc : Can f u) (w : E)
    (o : Nat) (g : List UInt64) :
    stepL f u w (restOf f l [(o, g.map Fld.ofF)]).toList = addOff f u o (sc f w g) := by
  apply ext_at0
  · rw [len_step f u _ w (by rw [len_rest, hu]; exact Nat.le_refl _), length_addOff]
  · intro i hi
    rw [len_step f u _ w (by rw [len_rest, hu]; exact Nat.le_refl _)] at hi
    rw [step_at f u _ w (by rw [len_rest, hu]; exact Nat.le_refl _) i hi,
      at0_rest1 f l o _ i (by omega), mulEF_zero_addE, mul_piece f w g l o i (by omega)]
    unfold pc
    by_cases h1 : o ≤ i ∧ i < o + (sc f w g).length
    · rw [if_pos h1.1, at0_addOff_in f u o _ i hi h1.1 h1.2]
    · rw [at0_addOff_out f u o _ i (by omega)]
      split
      · rw [at0_ge (sc f w g) (i - o) (by omega), addE_zero f _ (hc i)]
      · rw [addE_zero f _ (hc i)]

/-- A step with a row of two pieces that do not meet (`hd`), onto a list u of l entries that have
their words below p. -/
theorem step_rest2 (f : Fld) (l : Nat) (u : List E) (hu : u.length = l) (hc : Can f u) (w : E)
    (o o' : Nat) (g g' : List UInt64) (hd : o + g.length ≤ o') :
    stepL f u w (restOf f l [(o, g.map Fld.ofF), (o', g'.map Fld.ofF)]).toList =
      addOff f (addOff f u o (sc f w g)) o' (sc f w g') := by
  apply ext_at0
  · rw [len_step f u _ w (by rw [len_rest, hu]; exact Nat.le_refl _), length_addOff, length_addOff]
  · intro i hi
    rw [len_step f u _ w (by rw [len_rest, hu]; exact Nat.le_refl _)] at hi
    rw [step_at f u _ w (by rw [len_rest, hu]; exact Nat.le_refl _) i hi,
      at0_rest2 f l o o' _ _ i (by omega)]
    have hg : (sc f w g).length = g.length := length_sc f w g
    by_cases h2 : o' ≤ i
    · -- the first piece is over
      have e1 : at0 (layAt l o (g.map Fld.ofF)).toList i = Fld.zeroE := by
        rw [at0_layAt l o _ i (by omega), if_pos (by omega),
          at0_ge _ _ (by rw [List.length_map]; omega)]
      rw [e1, addE_zero_zero, mulEF_zero_addE, mul_piece f w g' l o' i (by omega)]
      unfold pc
      rw [if_pos h2]
      by_cases h3 : i < o' + (sc f w g').length
      · rw [at0_addOff_in f _ o' _ i (by rw [length_addOff]; exact hi) h2 h3,
          at0_addOff_out f u o _ i (by omega)]
      · rw [at0_addOff_out f _ o' _ i (by omega), at0_addOff_out f u o _ i (by omega),
          at0_ge (sc f w g') (i - o') (by omega), addE_zero f _ (hc i)]
    · have e2 : at0 (layAt l o' (g'.map Fld.ofF)).toList i = Fld.zeroE := by
        rw [at0_layAt l o' _ i (by omega), if_neg h2]
      rw [e2, mulEF_addE_zero, mulEF_zero_addE,
        mul_piece f w g l o i (by omega), at0_addOff_out f _ o' _ i (by omega)]
      unfold pc
      by_cases h1 : o ≤ i ∧ i < o + (sc f w g).length
      · rw [if_pos h1.1, at0_addOff_in f u o _ i hi h1.1 h1.2]
      · rw [at0_addOff_out f u o _ i (by omega)]
        split
        · rw [at0_ge (sc f w g) (i - o) (by omega), addE_zero f _ (hc i)]
        · rw [addE_zero f _ (hc i)]

/-! ## Seven pieces side by side, added in another order -/

theorem addOff_nil (f : Fld) (u : List E) (o : Nat) : addOff f u o [] = u := by
  apply ext_at0
  · rw [length_addOff]
  · intro i _
    exact at0_addOff_out f u o [] i (by simp; omega)

theorem addOff_append (f : Fld) (u : List E) (o : Nat) (b c : List E) :
    addOff f u o (b ++ c) = addOff f (addOff f u o b) (o + b.length) c := by
  apply ext_at0
  · rw [length_addOff, length_addOff, length_addOff]
  · intro i hi
    rw [length_addOff] at hi
    by_cases h1 : o ≤ i ∧ i < o + b.length
    · rw [at0_addOff_in f u o _ i hi h1.1 (by rw [List.length_append]; omega),
        at0_addOff_out f _ _ c i (by omega), at0_addOff_in f u o b i hi h1.1 h1.2,
        at0_append, if_pos (by omega)]
    · by_cases h2 : o + b.length ≤ i ∧ i < o + b.length + c.length
      · rw [at0_addOff_in f u o _ i hi (by omega) (by rw [List.length_append]; omega),
          at0_addOff_in f _ _ c i (by rw [length_addOff]; exact hi) h2.1 h2.2,
          at0_addOff_out f u o b i (by omega), at0_append, if_neg (by omega)]
        rw [show i - o - b.length = i - (o + b.length) by omega]
      · rw [at0_addOff_out f u o _ i (by rw [List.length_append]; omega),
          at0_addOff_out f _ _ c i (by omega), at0_addOff_out f u o b i (by omega)]

theorem seven (f : Fld) (u bA0 bA1 bT bTK bT0 bT1 bOP : List E) (A0 A1 T TK T0 T1 OP : Nat)
    (h0 : A0 = 0) (h1 : A1 = A0 + bA0.length) (h2 : T = A1 + bA1.length) (h3 : TK = T + bT.length)
    (h4 : T0 = TK + bTK.length) (h5 : T1 = T0 + bT0.length) (h6 : OP = T1 + bT1.length) :
    addOff f (addOff f
          (addOff f (addOff f (addOff f (addOff f (addOff f u T bT) TK bTK) OP bOP) A0 bA0) T0 bT0)
          A1 bA1)
        T1 bT1 =
      addOff f u 0 (bA0 ++ bA1 ++ bT ++ bTK ++ bT0 ++ bT1 ++ bOP) := by
  rw [addOff_append, addOff_append, addOff_append, addOff_append, addOff_append, addOff_append]
  simp only [List.length_append]
  apply ext_at0
  · simp only [length_addOff]
  · intro i hi
    simp only [length_addOff] at hi
    by_cases cA0 : A0 ≤ i ∧ i < A0 + bA0.length
    · rw [at0_addOff_out f _ T1 bT1 i (by omega),
        at0_addOff_out f _ A1 bA1 i (by omega),
        at0_addOff_out f _ T0 bT0 i (by omega),
        at0_addOff_in f _ A0 bA0 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ OP bOP i (by omega),
        at0_addOff_out f _ TK bTK i (by omega),
        at0_addOff_out f _ T bT i (by omega),
        at0_addOff_out f _ _ bOP i (by omega),
        at0_addOff_out f _ _ bT1 i (by omega),
        at0_addOff_out f _ _ bT0 i (by omega),
        at0_addOff_out f _ _ bTK i (by omega),
        at0_addOff_out f _ _ bT i (by omega),
        at0_addOff_out f _ _ bA1 i (by omega),
        at0_addOff_in f _ _ bA0 i hi (by omega) (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bA0 k)) (by omega)
    by_cases cA1 : A1 ≤ i ∧ i < A1 + bA1.length
    · rw [at0_addOff_out f _ T1 bT1 i (by omega),
        at0_addOff_in f _ A1 bA1 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ T0 bT0 i (by omega),
        at0_addOff_out f _ A0 bA0 i (by omega),
        at0_addOff_out f _ OP bOP i (by omega),
        at0_addOff_out f _ TK bTK i (by omega),
        at0_addOff_out f _ T bT i (by omega),
        at0_addOff_out f _ _ bOP i (by omega),
        at0_addOff_out f _ _ bT1 i (by omega),
        at0_addOff_out f _ _ bT0 i (by omega),
        at0_addOff_out f _ _ bTK i (by omega),
        at0_addOff_out f _ _ bT i (by omega),
        at0_addOff_in f _ _ bA1 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ _ bA0 i (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bA1 k)) (by omega)
    by_cases cT : T ≤ i ∧ i < T + bT.length
    · rw [at0_addOff_out f _ T1 bT1 i (by omega),
        at0_addOff_out f _ A1 bA1 i (by omega),
        at0_addOff_out f _ T0 bT0 i (by omega),
        at0_addOff_out f _ A0 bA0 i (by omega),
        at0_addOff_out f _ OP bOP i (by omega),
        at0_addOff_out f _ TK bTK i (by omega),
        at0_addOff_in f _ T bT i hi (by omega) (by omega),
        at0_addOff_out f _ _ bOP i (by omega),
        at0_addOff_out f _ _ bT1 i (by omega),
        at0_addOff_out f _ _ bT0 i (by omega),
        at0_addOff_out f _ _ bTK i (by omega),
        at0_addOff_in f _ _ bT i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ _ bA1 i (by omega),
        at0_addOff_out f _ _ bA0 i (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bT k)) (by omega)
    by_cases cTK : TK ≤ i ∧ i < TK + bTK.length
    · rw [at0_addOff_out f _ T1 bT1 i (by omega),
        at0_addOff_out f _ A1 bA1 i (by omega),
        at0_addOff_out f _ T0 bT0 i (by omega),
        at0_addOff_out f _ A0 bA0 i (by omega),
        at0_addOff_out f _ OP bOP i (by omega),
        at0_addOff_in f _ TK bTK i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ T bT i (by omega),
        at0_addOff_out f _ _ bOP i (by omega),
        at0_addOff_out f _ _ bT1 i (by omega),
        at0_addOff_out f _ _ bT0 i (by omega),
        at0_addOff_in f _ _ bTK i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ _ bT i (by omega),
        at0_addOff_out f _ _ bA1 i (by omega),
        at0_addOff_out f _ _ bA0 i (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bTK k)) (by omega)
    by_cases cT0 : T0 ≤ i ∧ i < T0 + bT0.length
    · rw [at0_addOff_out f _ T1 bT1 i (by omega),
        at0_addOff_out f _ A1 bA1 i (by omega),
        at0_addOff_in f _ T0 bT0 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ A0 bA0 i (by omega),
        at0_addOff_out f _ OP bOP i (by omega),
        at0_addOff_out f _ TK bTK i (by omega),
        at0_addOff_out f _ T bT i (by omega),
        at0_addOff_out f _ _ bOP i (by omega),
        at0_addOff_out f _ _ bT1 i (by omega),
        at0_addOff_in f _ _ bT0 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ _ bTK i (by omega),
        at0_addOff_out f _ _ bT i (by omega),
        at0_addOff_out f _ _ bA1 i (by omega),
        at0_addOff_out f _ _ bA0 i (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bT0 k)) (by omega)
    by_cases cT1 : T1 ≤ i ∧ i < T1 + bT1.length
    · rw [at0_addOff_in f _ T1 bT1 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ A1 bA1 i (by omega),
        at0_addOff_out f _ T0 bT0 i (by omega),
        at0_addOff_out f _ A0 bA0 i (by omega),
        at0_addOff_out f _ OP bOP i (by omega),
        at0_addOff_out f _ TK bTK i (by omega),
        at0_addOff_out f _ T bT i (by omega),
        at0_addOff_out f _ _ bOP i (by omega),
        at0_addOff_in f _ _ bT1 i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ _ bT0 i (by omega),
        at0_addOff_out f _ _ bTK i (by omega),
        at0_addOff_out f _ _ bT i (by omega),
        at0_addOff_out f _ _ bA1 i (by omega),
        at0_addOff_out f _ _ bA0 i (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bT1 k)) (by omega)
    by_cases cOP : OP ≤ i ∧ i < OP + bOP.length
    · rw [at0_addOff_out f _ T1 bT1 i (by omega),
        at0_addOff_out f _ A1 bA1 i (by omega),
        at0_addOff_out f _ T0 bT0 i (by omega),
        at0_addOff_out f _ A0 bA0 i (by omega),
        at0_addOff_in f _ OP bOP i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ TK bTK i (by omega),
        at0_addOff_out f _ T bT i (by omega),
        at0_addOff_in f _ _ bOP i (by simp only [length_addOff]; exact hi) (by omega) (by omega),
        at0_addOff_out f _ _ bT1 i (by omega),
        at0_addOff_out f _ _ bT0 i (by omega),
        at0_addOff_out f _ _ bTK i (by omega),
        at0_addOff_out f _ _ bT i (by omega),
        at0_addOff_out f _ _ bA1 i (by omega),
        at0_addOff_out f _ _ bA0 i (by omega)]
      exact congrArg (fun k => f.addE (at0 u i) (at0 bOP k)) (by omega)
    rw [at0_addOff_out f _ T1 bT1 i (by omega),
      at0_addOff_out f _ A1 bA1 i (by omega),
      at0_addOff_out f _ T0 bT0 i (by omega),
      at0_addOff_out f _ A0 bA0 i (by omega),
      at0_addOff_out f _ OP bOP i (by omega),
      at0_addOff_out f _ TK bTK i (by omega),
      at0_addOff_out f _ T bT i (by omega),
      at0_addOff_out f _ _ bOP i (by omega),
      at0_addOff_out f _ _ bT1 i (by omega),
      at0_addOff_out f _ _ bT0 i (by omega),
      at0_addOff_out f _ _ bTK i (by omega),
      at0_addOff_out f _ _ bT i (by omega),
      at0_addOff_out f _ _ bA1 i (by omega),
      at0_addOff_out f _ _ bA0 i (by omega)]

/-! ## One draw -/

/-- the fast form's state as the literal form's -/
def toL (l : Nat) (st : List E × List E × List E × E × E) : LRow × E :=
  (⟨twoRows l st.1.toArray st.2.1.toArray, st.2.2.1.toArray, st.2.2.2.1⟩, st.2.2.2.2)

/-- the literal form's step -/
def stL (f : Fld) (theta : E) (s : LRow × E) (r : LRow) : LRow × E :=
  (s.1.add f s.2 r, f.mulE s.2 theta)

def InvL (f : Fld) (l : Nat) (kept : Bool) (st : List E × List E × List E × E × E) : Prop :=
  st.1.length = l ∧ st.2.1.length = l ∧ st.2.2.1.length = (if kept then l else 0) ∧ Can f st.1 ∧
  Can f st.2.1 ∧ Can f st.2.2.1

theorem add_toL (f : Fld) (theta : E) (l : Nat) (r0 r1 p X Y q : List E) (t w t' : E)
    (h0 : r0.length = l) (h1 : r1.length = l) (hX : X.length ≤ l) (hY : Y.length ≤ l) :
    stL f theta (toL l (r0, r1, p, t, w)) ⟨twoRows l X.toArray Y.toArray, q.toArray, t'⟩ =
      toL l (stepL f r0 w X, stepL f r1 w Y, stepL f p w q,
          f.addE t (f.mulE w t'), f.mulE w theta) := by
  have e := tw_step f l r0 r1 X Y w h0 h1 hX hY
  show ((⟨(stepL f (tw l r0 r1) w (tw l X Y)).toArray,
        (stepL f p w q).toArray,
        f.addE t (f.mulE w t')⟩ : LRow),
      f.mulE w theta) = _
  rw [e]
  rfl

theorem step_pre (f : Fld) (u : List E) (hc : Can f u) (w : E)
    (g : List UInt64) (hg : g.length ≤ u.length) :
    stepL f u w (g.map Fld.ofF) = addPre f u (sc f w g) := by
  apply ext_at0
  · rw [len_step f u _ w (by rw [List.length_map]; exact hg), length_addPre]
  · intro i hi
    rw [len_step f u _ w (by rw [List.length_map]; exact hg)] at hi
    rw [step_at f u _ w (by rw [List.length_map]; exact hg) i hi,
      mulEF_at0_ofF, at0_addPre f u _ i hi]
    split
    · rfl
    · rw [at0_ge (sc f w g) i (by omega), addE_zero f _ (hc i)]

theorem at0_toArr (l : List E) (i : Nat) : ent l.toArray i = at0 l i := by
  unfold ent at0
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]

theorem at0_ofF (g : List UInt64) (i : Nat) (h : i < g.length) :
    at0 (g.map Fld.ofF) i = Fld.ofF g[i] :=
  at0_mapU Fld.ofF g i h

/-- The old pad's three coefficients are the generator's last three, if the generator's row g has l
entries (`hg`) and l is at least three (`h3`). -/
theorem overPad_eq (l : Nat) (g : List UInt64) (hg : g.length = l) (h3 : 3 ≤ l) :
    overPad l (g.map Fld.ofF).toArray = (g.drop (l - 3)).map Fld.ofF := by
  apply ext_at0
  · rw [List.length_map, List.length_drop, hg]
    show 3 = l - (l - 3)
    omega
  · intro i hi
    have hi3 : i < 3 := hi
    rw [List.map_drop, at0_drop]
    unfold overPad
    rw [at0_toArr, at0_toArr, at0_toArr]
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · rfl
    · show at0 _ (l - 2) = at0 _ (l - 3 + 1)
      rw [show l - 3 + 1 = l - 2 by omega]
    · show at0 _ (l - 1) = at0 _ (l - 3 + 2)
      rw [show l - 3 + 2 = l - 1 by omega]

theorem length_overP (l : Nat) (Q : Array E) : (overP l Q).toList.length = l := by
  unfold overP
  simp

theorem at0_overP (l : Nat) (Q : List E) (i : Nat) (h : i < l) :
    at0 (overP l Q.toArray).toList i = if i + 3 < l then at0 Q i else Fld.zeroE := by
  unfold overP
  conv => lhs; unfold at0
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getElem?_ofFn, dif_pos h]
  simp only [Option.getD_some]
  split
  · exact at0_toArr Q i
  · rfl

/-- a step with the generator's row carried over to the second sending -/
theorem step_overP (f : Fld) (l : Nat) (p : List E) (hp : p.length = l) (hc : Can f p) (w : E)
    (g : List UInt64) (hg : g.length = l) :
    stepL f p w (overP l (g.map Fld.ofF).toArray).toList =
      addPre f p (sc f w (g.take (l - 3))) := by
  apply ext_at0
  · rw [len_step f p _ w (by rw [length_overP, hp]; exact Nat.le_refl _), length_addPre]
  · intro i hi
    rw [len_step f p _ w (by rw [length_overP, hp]; exact Nat.le_refl _)] at hi
    rw [step_at f p _ w (by rw [length_overP, hp]; exact Nat.le_refl _) i hi,
      at0_overP l _ i (by omega), at0_addPre f p _ i hi, length_sc, List.length_take, hg]
    by_cases h : i + 3 < l
    · rw [if_pos h, if_pos (by omega), mulEF_at0_ofF]
      congr 1
      unfold sc
      rw [List.map_take, at0_take _ _ _ (by omega)]
    · rw [if_neg h, if_neg (by omega), mulEF_zero, addE_zero f _ (hc i)]

/-- the four rows' parts on row 1 of the carrying message -/
def Y1 (f : Fld) (C Z : Code) (kept : Bool) (x : Nat) : List E :=
  (restOf f C.l [((restOff C Z kept).T, (genT C x).map Fld.ofF)]).toList
def Y2 (f : Fld) (C Z : Code) (x : Nat) : List E :=
  (restOf f C.l
    [((restOff C Z true).TK, (genT C x).map Fld.ofF),
      ((restOff C Z true).OP, overPad C.l ((genM C x).map Fld.ofF).toArray)]).toList
def Y3 (f : Fld) (C Z : Code) (kept : Bool) (x : Nat) : List E :=
  (restOf f C.l
    [((restOff C Z kept).A0, (genM Z (cp Z x)).map Fld.ofF),
      ((restOff C Z kept).T0, (genT Z (cp Z x)).map Fld.ofF)]).toList
def Y4 (f : Fld) (C Z : Code) (kept : Bool) (x : Nat) : List E :=
  (restOf f C.l
    [((restOff C Z kept).A1, (genM Z (cp Z x)).map Fld.ofF),
      ((restOff C Z kept).T1, (genT Z (cp Z x)).map Fld.ofF)]).toList

theorem drawL_true (f : Fld) (C Z : Code) (S : KSRow) (x : Nat) (cl : KCol) :
    drawL f C Z true S x cl =
      [⟨twoRows C.l ((genM C x).map Fld.ofF).toArray (Y1 f C Z true x).toArray,
          ([] : List E).toArray,
          (yOf f 0 S.s cl.col).1⟩,
        ⟨twoRows C.l ([] : List E).toArray (Y2 f C Z x).toArray,
          (overP C.l ((genM C x).map Fld.ofF).toArray).toList.toArray,
          cl.kept.getD Fld.zeroE⟩,
        ⟨twoRows C.l ([] : List E).toArray (Y3 f C Z true x).toArray,
          ([] : List E).toArray,
          (yOf f 0 S.s cl.col).2.1⟩,
        ⟨twoRows C.l ([] : List E).toArray (Y4 f C Z true x).toArray,
          ([] : List E).toArray,
          (yOf f 0 S.s cl.col).2.2⟩] := rfl

theorem drawL_false (f : Fld) (C Z : Code) (S : KSRow) (x : Nat) (cl : KCol) :
    drawL f C Z false S x cl =
      [⟨twoRows C.l ((genM C x).map Fld.ofF).toArray (Y1 f C Z false x).toArray,
          ([] : List E).toArray,
          (yOf f 0 S.s cl.col).1⟩,
        ⟨twoRows C.l ([] : List E).toArray (Y3 f C Z false x).toArray,
          ([] : List E).toArray,
          (yOf f 0 S.s cl.col).2.1⟩,
        ⟨twoRows C.l ([] : List E).toArray (Y4 f C Z false x).toArray,
          ([] : List E).toArray,
          (yOf f 0 S.s cl.col).2.2⟩] := rfl

theorem lenY1 (f : Fld) (C Z : Code) (kept : Bool) (x : Nat) : (Y1 f C Z kept x).length = C.l :=
  len_rest f _ _
theorem lenY2 (f : Fld) (C Z : Code) (x : Nat) : (Y2 f C Z x).length = C.l := len_rest f _ _
theorem lenY3 (f : Fld) (C Z : Code) (kept : Bool) (x : Nat) : (Y3 f C Z kept x).length = C.l :=
  len_rest f _ _
theorem lenY4 (f : Fld) (C Z : Code) (kept : Bool) (x : Nat) : (Y4 f C Z kept x).length = C.l :=
  len_rest f _ _

/-- Row 1 after a draw with a kept row. -/
theorem row1_true (f : Fld) (C Z : Code) (x : Nat) (u : List E) (hu : u.length = C.l) (hc : Can f u)
    (h3 : 3 ≤ C.l) (w0 wK wO wF : E) :
    stepL f
        (stepL f (stepL f (stepL f u w0 (Y1 f C Z true x)) wK (Y2 f C Z x)) wO (Y3 f C Z true x)) wF
        (Y4 f C Z true x) =
      addPre f u
        (sc f wO (genM Z (cp Z x)) ++ sc f wF (genM Z (cp Z x)) ++ sc f w0 (genT C x) ++
          sc f wK (genT C x) ++ sc f wO (genT Z (cp Z x)) ++ sc f wF (genT Z (cp Z x)) ++
          sc f wK ((genM C x).drop (C.l - 3))) := by
  have a1 : (genM C x).length = C.l := length_genM C x
  have a2 : (genT C x).length = C.r := length_genT C x
  have a3 : (genM Z (cp Z x)).length = Z.l := length_genM Z _
  have a4 : (genT Z (cp Z x)).length = Z.r := length_genT Z _
  unfold Y1 Y2 Y3 Y4
  rw [overPad_eq C.l (genM C x) a1 h3, step_rest1 f C.l u hu hc w0,
    step_rest2 f C.l _ (by rw [length_addOff]; exact hu) (can_addOff f _ _ _ hc) wK _ _ _ _
      (by rw [a2]; show 2 * Z.l + C.r + C.r ≤ 2 * Z.l + C.r + C.r + 2 * Z.r; omega),
    step_rest2 f C.l _ (by simp only [length_addOff]; exact hu)
      (can_addOff f _ _ _ (can_addOff f _ _ _ (can_addOff f _ _ _ hc))) wO _ _ _ _
      (by rw [a3]; simp only [restOff]; omega),
    step_rest2 f C.l _ (by simp only [length_addOff]; exact hu)
      (can_addOff f _ _ _
        (can_addOff f _ _ _ (can_addOff f _ _ _ (can_addOff f _ _ _ (can_addOff f _ _ _ hc)))))
      wF _ _ _ _ (by rw [a3]; simp only [restOff]; omega), addPre_off]
  exact seven f u _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
    (by rw [length_sc, a3]; simp only [restOff]; omega)
    (by rw [length_sc, a3]; simp only [restOff]; omega) (by rw [length_sc, a2]; simp only [restOff])
    (by rw [length_sc, a2]; simp only [restOff]; simp) (by rw [length_sc, a4]; simp only [restOff])
    (by rw [length_sc, a4]; simp only [restOff]; omega)

/-- Row 1 after a draw without a kept row. -/
theorem row1_false (f : Fld) (C Z : Code) (x : Nat) (u : List E) (hu : u.length = C.l)
    (hc : Can f u) (w0 wO wF : E) :
    stepL f (stepL f (stepL f u w0 (Y1 f C Z false x)) wO (Y3 f C Z false x)) wF
        (Y4 f C Z false x) =
      addPre f u
        (sc f wO (genM Z (cp Z x)) ++ sc f wF (genM Z (cp Z x)) ++ sc f w0 (genT C x) ++ [] ++
          sc f wO (genT Z (cp Z x)) ++ sc f wF (genT Z (cp Z x)) ++ []) := by
  have a2 : (genT C x).length = C.r := length_genT C x
  have a3 : (genM Z (cp Z x)).length = Z.l := length_genM Z _
  have a4 : (genT Z (cp Z x)).length = Z.r := length_genT Z _
  unfold Y1 Y3 Y4
  rw [step_rest1 f C.l u hu hc w0,
    step_rest2 f C.l _ (by simp only [length_addOff]; exact hu) (can_addOff f _ _ _ hc) wO _ _ _ _
      (by rw [a3]; simp only [restOff]; omega),
    step_rest2 f C.l _ (by simp only [length_addOff]; exact hu)
      (can_addOff f _ _ _ (can_addOff f _ _ _ (can_addOff f _ _ _ hc))) wF _ _ _ _
      (by rw [a3]; simp only [restOff]; omega), addPre_off]
  have s := seven f u (sc f wO (genM Z (cp Z x))) (sc f wF (genM Z (cp Z x))) (sc f w0 (genT C x))
    [] (sc f wO (genT Z (cp Z x))) (sc f wF (genT Z (cp Z x))) [] (restOff C Z false).A0
    (restOff C Z false).A1 (restOff C Z false).T (restOff C Z false).TK (restOff C Z false).T0
    (restOff C Z false).T1 (restOff C Z false).OP rfl
    (by rw [length_sc, a3]; simp only [restOff]; omega)
    (by rw [length_sc, a3]; simp only [restOff]; omega) (by rw [length_sc, a2]; simp only [restOff])
    (by simp [restOff]) (by rw [length_sc, a4]; simp only [restOff])
    (by rw [length_sc, a4]; simp only [restOff]; omega)
  rw [addOff_nil, addOff_nil] at s
  exact s

theorem can_nil (f : Fld) : Can f [] := fun _ => okE_zero f

/-- One draw, with a kept row. -/
theorem draw_true (f : Fld) (C Z : Code) (S : KSRow) (theta : E) (x : Nat) (cl : KCol)
    (r0 r1 p : List E) (t w0 : E) (h : InvL f C.l true (r0, r1, p, t, w0)) (h3 : 3 ≤ C.l) :
    (drawL f C Z true S x cl).foldl (stL f theta) (toL C.l (r0, r1, p, t, w0)) =
      toL C.l (addDrawL f C Z true S theta x cl (r0, r1, p, t, w0)) := by
  obtain ⟨l0, l1, lp, c0, c1, cP⟩ := h
  have l0' : r0.length = C.l := l0
  have l1' : r1.length = C.l := l1
  have lp' : p.length = C.l := lp
  have a1 : (genM C x).length = C.l := length_genM C x
  rw [drawL_true]
  simp only [List.foldl]
  rw [add_toL f theta C.l r0 r1 p _ _ _ t w0 _ l0' l1'
        (by rw [List.length_map, a1]; exact Nat.le_refl _) (by rw [lenY1]; exact Nat.le_refl _),
    add_toL f theta C.l _ _ _ _ _ _ _ _ _
      (by
        rw [len_step f r0 _ w0 (by rw [List.length_map, a1, l0']; exact Nat.le_refl _)]; exact l0')
      (by rw [len_step f r1 _ w0 (by rw [lenY1, l1']; exact Nat.le_refl _)]; exact l1')
      (Nat.zero_le _) (by rw [lenY2]; exact Nat.le_refl _)]
  rw [step_pre f r0 c0 w0 (genM C x) (by rw [a1, l0']; exact Nat.le_refl _), step_nil f p w0 cP,
    step_nil f _ _ (can_addPre f _ _ c0), step_overP f C.l p lp' cP _ (genM C x) a1]
  rw [add_toL f theta C.l _ _ _ _ _ _ _ _ _ (by rw [length_addPre]; exact l0') (by rw [len_step f _ _ _ (by rw [lenY2, len_step f r1 _ w0 (by rw [lenY1, l1']; exact Nat.le_refl _), l1']; exact Nat.le_refl _), len_step f r1 _ w0 (by rw [lenY1, l1']; exact Nat.le_refl _)]; exact l1') (Nat.zero_le _) (by rw [lenY3]; exact Nat.le_refl _)]
  rw [step_nil f _ _ (can_addPre f _ _ c0), step_nil f _ _ (can_addPre f _ _ cP)]
  rw [add_toL f theta C.l _ _ _ _ _ _ _ _ _ (by rw [length_addPre]; exact l0')
      (by simp only [length_stepL, lenY1, lenY2, lenY3, l1']; omega)
      (Nat.zero_le _) (by rw [lenY4]; exact Nat.le_refl _)]
  rw [step_nil f _ _ (can_addPre f _ _ c0),
    step_nil f _ _ (can_addPre f _ _ cP), row1_true f C Z x r1 l1' c1 h3]
  rfl

/-- One draw, without a kept row. -/
theorem draw_false (f : Fld) (C Z : Code) (S : KSRow) (theta : E) (x : Nat) (cl : KCol)
    (r0 r1 p : List E) (t w0 : E) (h : InvL f C.l false (r0, r1, p, t, w0)) :
    (drawL f C Z false S x cl).foldl (stL f theta) (toL C.l (r0, r1, p, t, w0)) =
      toL C.l (addDrawL f C Z false S theta x cl (r0, r1, p, t, w0)) := by
  obtain ⟨l0, l1, lp, c0, c1, cP⟩ := h
  have l0' : r0.length = C.l := l0
  have l1' : r1.length = C.l := l1
  have a1 : (genM C x).length = C.l := length_genM C x
  rw [drawL_false]
  simp only [List.foldl]
  rw [add_toL f theta C.l r0 r1 p _ _ _ t w0 _ l0' l1'
      (by rw [List.length_map, a1]; exact Nat.le_refl _) (by rw [lenY1]; exact Nat.le_refl _)]
  rw [step_pre f r0 c0 w0 (genM C x) (by rw [a1, l0']; exact Nat.le_refl _), step_nil f p w0 cP]
  rw [add_toL f theta C.l _ _ _ _ _ _ _ _ _ (by rw [length_addPre]; exact l0')
      (by rw [len_step f r1 _ w0 (by rw [lenY1, l1']; exact Nat.le_refl _)]; exact l1')
      (Nat.zero_le _) (by rw [lenY3]; exact Nat.le_refl _)]
  rw [step_nil f _ _ (can_addPre f _ _ c0), step_nil f p _ cP]
  rw [add_toL f theta C.l _ _ _ _ _ _ _ _ _ (by rw [length_addPre]; exact l0')
      (by simp only [length_stepL, lenY1, lenY3, l1']; omega) (Nat.zero_le _)
      (by rw [lenY4]; exact Nat.le_refl _)]
  rw [step_nil f _ _ (can_addPre f _ _ c0), step_nil f p _ cP, row1_false f C Z x r1 l1' c1]
  show toL C.l (_, _, p, f.addE (f.addE (f.addE t (f.mulE w0 (yOf f 0 S.s cl.col).1)) _) _, _) =
    toL C.l (_, _, p,
        f.addE (f.addE (f.addE (f.addE t (f.mulE w0 (yOf f 0 S.s cl.col).1)) Fld.zeroE) _) _, _)
  rw [addE_zero f _ (okE_addE f _ _)]
  rfl

theorem draw_any (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (x : Nat) (cl : KCol)
    (st : List E × List E × List E × E × E) (h : InvL f C.l kept st) (h3 : kept = true → 3 ≤ C.l) :
    (drawL f C Z kept S x cl).foldl (stL f theta) (toL C.l st) =
      toL C.l (addDrawL f C Z kept S theta x cl st) := by
  obtain ⟨r0, r1, p, t, w0⟩ := st
  cases kept with
  | true => exact draw_true f C Z S theta x cl r0 r1 p t w0 h (h3 rfl)
  | false => exact draw_false f C Z S theta x cl r0 r1 p t w0 h

theorem inv_any (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (x : Nat) (cl : KCol)
    (st : List E × List E × List E × E × E) (h : InvL f C.l kept st) :
    InvL f C.l kept (addDrawL f C Z kept S theta x cl st) := by
  obtain ⟨r0, r1, p, t, w0⟩ := st
  obtain ⟨l0, l1, lp, c0, c1, cP⟩ := h
  cases kept with
  | true =>
    exact ⟨(length_addPre f _ _).trans l0, (length_addPre f _ _).trans l1,
      (length_addPre f _ _).trans lp, can_addPre f _ _ c0, can_addPre f _ _ c1, can_addPre f _ _ cP⟩
  | false =>
    exact ⟨(length_addPre f _ _).trans l0, (length_addPre f _ _).trans l1,
      lp, can_addPre f _ _ c0, can_addPre f _ _ c1, cP⟩

/-! ## All draws -/

def litFold (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (col : Nat → Option KCol)
    (a : Option (LRow × E)) (xs : List Nat) : Option (LRow × E) :=
  xs.foldl (fun (acc : Option (LRow × E)) x =>
    match acc, col x with
    | some a, some cl =>
      some ((drawL f C Z kept S x cl).foldl
          (fun (s : LRow × E) r => (s.1.add f s.2 r, f.mulE s.2 theta)) a)
    | _, _ => none) a

def fastFold (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (col : Nat → Option KCol)
    (a : Option (List E × List E × List E × E × E)) (xs : List Nat) :
    Option (List E × List E × List E × E × E) :=
  xs.foldl (fun (acc : Option (List E × List E × List E × E × E)) x =>
    match acc, col x with
    | some st, some cl => some (addDrawL f C Z kept S theta x cl st)
    | _, _ => none) a

theorem litFold_none (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow)
    (theta : E) (col : Nat → Option KCol) :
    ∀ xs, litFold f C Z kept S theta col none xs = none
  | [] => rfl
  | _ :: xs => litFold_none f C Z kept S theta col xs

theorem fastFold_none (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow)
    (theta : E) (col : Nat → Option KCol) :
    ∀ xs, fastFold f C Z kept S theta col none xs = none
  | [] => rfl
  | _ :: xs => fastFold_none f C Z kept S theta col xs

theorem all_draws (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E)
    (col : Nat → Option KCol) (h3 : kept = true → 3 ≤ C.l) :
    ∀ (xs : List Nat) (st : List E × List E × List E × E × E), InvL f C.l kept st →
      litFold f C Z kept S theta col (some (toL C.l st)) xs =
        (fastFold f C Z kept S theta col (some st) xs).map (toL C.l)
  | [], _, _ => rfl
  | x :: xs, st, h => by
      cases hc : col x with
      | none =>
          have e1 : litFold f C Z kept S theta col (some (toL C.l st)) (x :: xs) =
              litFold f C Z kept S theta col none xs := by
            show litFold f C Z kept S theta col (match some (toL C.l st), col x with
              | some a, some cl =>
                some ((drawL f C Z kept S x cl).foldl
                    (fun (s : LRow × E) r => (s.1.add f s.2 r, f.mulE s.2 theta)) a)
              | _, _ => none) xs = _
            rw [hc]
          have e2 : fastFold f C Z kept S theta col (some st) (x :: xs) =
              fastFold f C Z kept S theta col none xs := by
            show fastFold f C Z kept S theta col (match some st, col x with
              | some st, some cl => some (addDrawL f C Z kept S theta x cl st)
              | _, _ => none) xs = _
            rw [hc]
          rw [e1, e2, litFold_none, fastFold_none]
          rfl
      | some cl =>
          have e1 : litFold f C Z kept S theta col (some (toL C.l st)) (x :: xs) =
              litFold f C Z kept S theta col
                (some ((drawL f C Z kept S x cl).foldl (stL f theta) (toL C.l st))) xs := by
            show litFold f C Z kept S theta col (match some (toL C.l st), col x with
              | some a, some cl =>
                some ((drawL f C Z kept S x cl).foldl
                    (fun (s : LRow × E) r => (s.1.add f s.2 r, f.mulE s.2 theta)) a)
              | _, _ => none) xs = _
            rw [hc]
            rfl
          have e2 : fastFold f C Z kept S theta col (some st) (x :: xs) =
              fastFold f C Z kept S theta col (some (addDrawL f C Z kept S theta x cl st)) xs := by
            show fastFold f C Z kept S theta col (match some st, col x with
              | some st, some cl => some (addDrawL f C Z kept S theta x cl st)
              | _, _ => none) xs = _
            rw [hc]
          rw [e1, e2, draw_any f C Z kept S theta x cl st h h3]
          exact all_draws f C Z kept S theta col h3 xs _ (inv_any f C Z kept S theta x cl st h)

/-! ## The whole -/

theorem at0_replicate (n i : Nat) : at0 (List.replicate n Fld.zeroE) i = Fld.zeroE := by
  unfold at0
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_replicate_of_lt h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_replicate]; omega)]
    rfl

theorem can_replicate (f : Fld) (n : Nat) : Can f (List.replicate n Fld.zeroE) := fun i => by
  rw [at0_replicate]
  exact okE_zero f

theorem tw_zero (l : Nat) :
    twoRows l (List.replicate l Fld.zeroE).toArray (List.replicate l Fld.zeroE).toArray =
      zerosE (2 * l) := by
  have e : tw l (List.replicate l Fld.zeroE) (List.replicate l Fld.zeroE) =
      (zerosE (2 * l)).toList := by
    apply ext_at0
    · rw [length_tw, length_zerosE]
    · intro i hi
      rw [length_tw] at hi
      rw [at0_tw l _ _ i hi, at0_zerosE]
      split <;> exact at0_replicate _ _
  exact congrArg List.toArray e

def Spec.sumDraws_eq : Prop :=
  ∀ (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta first : E)
      (xs : List Nat) (col : Nat → Option KCol),
    (kept = true → 3 ≤ C.l) →
    sumDraws f C Z kept S theta first xs col = sumDrawsLit f C Z kept S theta first xs col

/-- Proves `Spec.sumDraws_eq`: if, where there is a kept row, a row has at least three places, the
fast sum of the draws' rows is its meaning. -/
theorem sumDraws_eq : Spec.sumDraws_eq := by
  intro f C Z kept S theta first xs col h3
  have hI : InvL f C.l kept
      (List.replicate C.l Fld.zeroE, List.replicate C.l Fld.zeroE,
        if kept then List.replicate C.l Fld.zeroE else [], Fld.zeroE, first) := by
    refine ⟨List.length_replicate, List.length_replicate, ?_,
      can_replicate f _, can_replicate f _, ?_⟩
    · cases kept
      · rfl
      · exact List.length_replicate
    · cases kept
      · exact can_nil f
      · exact can_replicate f _
  have h0 : toL C.l
        (List.replicate C.l Fld.zeroE, List.replicate C.l Fld.zeroE,
          if kept then List.replicate C.l Fld.zeroE else [], Fld.zeroE, first) =
      (⟨zerosE (2 * C.l), if kept then zerosE C.l else #[], Fld.zeroE⟩, first) := by
    unfold toL
    dsimp only
    rw [tw_zero]
    cases kept
    · rfl
    · show _ = ((⟨zerosE (2 * C.l), zerosE C.l, Fld.zeroE⟩ : LRow), first)
      unfold zerosE
      simp
  have hA := all_draws f C Z kept S theta col h3 xs _ hI
  rw [h0] at hA
  exact hA.symm

/-! ## Onto a row that is there already -/

theorem length_rowOfG (l b : Nat) (g : Array E) : (rowOfG l b g).length = l := by
  unfold rowOfG
  rw [List.length_map, List.length_range]

theorem at0_rowOfG (l b : Nat) (g : Array E) (j : Nat) (h : j < l) :
    at0 (rowOfG l b g) j = at0 g.toList (b + 2 * j) := by
  unfold rowOfG
  conv => lhs; unfold at0
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  show ent g (b + 2 * j) = _
  exact at0_toArr g.toList _

theorem can_rowOfG (f : Fld) (l b : Nat) (g : Array E) (h : Can f g.toList) :
    Can f (rowOfG l b g) := by
  intro j
  by_cases hj : j < l
  · rw [at0_rowOfG l b g j hj]
    exact h _
  · rw [at0_ge _ _ (by rw [length_rowOfG]; omega)]
    exact okE_zero f

/-- A table of 2 l entries is made of its two rows. -/
theorem tw_rows (l : Nat) (g : Array E) (h : g.size = 2 * l) :
    twoRows l (rowOfG l 0 g).toArray (rowOfG l 1 g).toArray = g := by
  have e : tw l (rowOfG l 0 g) (rowOfG l 1 g) = g.toList := by
    apply ext_at0
    · rw [length_tw, Array.length_toList, h]
    · intro i hi
      rw [length_tw] at hi
      rw [at0_tw l _ _ i hi]
      split
      · rw [at0_rowOfG l 0 g _ (by omega), show 0 + 2 * (i / 2) = i by omega]
      · rw [at0_rowOfG l 1 g _ (by omega), show 1 + 2 * (i / 2) = i by omega]
  exact congrArg List.toArray e

def Spec.sumDrawsFrom_eq : Prop :=
  ∀ (f : Fld) (C Z : Code) (kept : Bool) (S : KSRow) (theta : E) (start : LRow) (first : E)
      (xs : List Nat) (col : Nat → Option KCol),
    (kept = true → 3 ≤ C.l) → start.g.size = 2 * C.l → start.p.size = (if kept then C.l else 0) →
    Can f start.g.toList → Can f start.p.toList →
    sumDrawsFrom f C Z kept S theta start first xs col =
      sumDrawsFromLit f C Z kept S theta start first xs col

/-- Proves `Spec.sumDrawsFrom_eq`: the same, under the same condition on the sizes, from any start
of the right lengths whose entries have their words below p. -/
theorem sumDrawsFrom_eq : Spec.sumDrawsFrom_eq := by
  intro f C Z kept S theta start first xs col h3 hg hp cg cp'
  have hI : InvL f C.l kept
      (rowOfG C.l 0 start.g, rowOfG C.l 1 start.g, start.p.toList, start.t, first) :=
    ⟨length_rowOfG _ _ _, length_rowOfG _ _ _, by rw [Array.length_toList]; exact hp,
      can_rowOfG f _ _ _ cg, can_rowOfG f _ _ _ cg, cp'⟩
  have h0 : toL C.l (rowOfG C.l 0 start.g, rowOfG C.l 1 start.g, start.p.toList, start.t, first) =
      (start, first) := by
    unfold toL
    dsimp only
    rw [tw_rows C.l start.g hg]
  have hA := all_draws f C Z kept S theta col h3 xs _ hI
  rw [h0] at hA
  exact hA.symm

end Fmt.M2.LocEq
