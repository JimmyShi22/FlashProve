-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/FoldTri.lean: the 2 k + 1 coefficients of a hiding polynomial and the 2 k + 1
values of its k rounds determine each other. A map forth, a map back, and both round
trips. Pure algebra over any commutative ring: nothing is divided.
Terms of this folder: Johnson/LinkSim/Spec.lean.

The setting. A hiding polynomial (Johnson/LinkSim/AtText/Defs.lean's terms) has k variables. Each
variable has a linear and a quadratic coefficient (a, b), and there is one constant c. The values of
its k rounds are its sum over the cube and, for each variable in turn, the constant and the
quadratic coefficient of that round's polynomial.

What this file has.
  mu l c        the sum: (a + b) + 2 (the sum of the rest); c where no variable is left.
  shownW l c    for each variable: (the sum of the rest, b).
  unW s r       the map back, from the sum s and the rounds' pairs r to the coefficients and the
                constant: a = (the value in front) - b - 2 (the round's constant).
  unW_shown     back after forth gives the coefficients again.
  mu_unW, shownW_unW   forth after back gives the values again.
  shiftW, shown_shiftW   the consequence. For any change (ds, dr) of the values, with as many pairs
                as variables, adding unW ds dr to the coefficients changes the values by exactly
                that.

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/FoldShift.lean carries shown_shiftW over to the library's names.

Other names (namespace OnBytes.LinkSim).
  length_shownW, length_unW   as many pairs as variables.
  addW, mu_addW, shownW_addW  the map forth is additive, for two lists of the same length.
  mu_two        an example over the integers: at one variable, (a, b) = (1, 2) and c = 3, the sum
                is 9, the round holds (3, 2), and the map back gives (1, 2) and 3.
  mu_char_two   the same in a ring where 2 = 0: nothing is divided.

Limits. The round's linear coefficient is not among the values. Lists of two lengths are not added.

Sources. mu and shownW follow the shape of the library's sum of a hiding polynomial and of its round
polynomials at plain variables of degree 2 (hMu, hRc, hTr, HVar.plain, Cb/Ld/LdHide.lean): nodes 0
and 1 with the weight 1.

Notes. That they are these functions at such variables is not proved here. It is proved in
Johnson/LinkSim/FoldTriTie.lean (hMu_list, hTr_list).
Terms: lean/GLOSSARY.md.

-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace OnBytes.LinkSim

variable {R : Type} [CommRing R]

/-- The sum over the cube: (a + b) + 2 (the sum of the rest), and c at no variable. -/
def mu : List (R × R) → R → R
  | [], c => c
  | x :: l, c => (x.1 + x.2) + 2 * mu l c

/-- What the rounds hold: for each variable, the sum of the rest and b. -/
def shownW : List (R × R) → R → List (R × R)
  | [], _ => []
  | x :: l, c => (mu l c, x.2) :: shownW l c

/-- The map back from the sum and the rounds' pairs to the coefficients and the constant. -/
def unW : R → List (R × R) → List (R × R) × R
  | s, [] => ([], s)
  | s, y :: r => ((s - y.2 - 2 * y.1, y.2) :: (unW y.1 r).1, (unW y.1 r).2)

/-- shownW gives one pair per variable. -/
theorem length_shownW : ∀ (l : List (R × R)) (c : R), (shownW l c).length = l.length
  | [], _ => rfl
  | _ :: l, c => congrArg (· + 1) (length_shownW l c)

/-- unW gives one pair per round. -/
theorem length_unW : ∀ (r : List (R × R)) (s : R), (unW s r).1.length = r.length
  | [], _ => rfl
  | y :: r, _ => congrArg (· + 1) (length_unW r y.1)

/-- Back after forth gives the coefficients and the constant. -/
theorem unW_shown : ∀ (l : List (R × R)) (c : R), unW (mu l c) (shownW l c) = (l, c)
  | [], _ => rfl
  | x :: l, c => by
      show ((x.1 + x.2 + 2 * mu l c - x.2 - 2 * mu l c, x.2) :: (unW (mu l c) (shownW l c)).1,
        (unW (mu l c) (shownW l c)).2) = (x :: l, c)
      rw [unW_shown l c]
      have e : x.1 + x.2 + 2 * mu l c - x.2 - 2 * mu l c = x.1 := by ring
      rw [e]

/-- Forth after back gives the sum again. -/
theorem mu_unW : ∀ (r : List (R × R)) (s : R), mu (unW s r).1 (unW s r).2 = s
  | [], _ => rfl
  | y :: r, s => by
      show (s - y.2 - 2 * y.1 + y.2) + 2 * mu (unW y.1 r).1 (unW y.1 r).2 = s
      rw [mu_unW r y.1]
      ring

/-- Forth after back gives the rounds' pairs again. -/
theorem shownW_unW : ∀ (r : List (R × R)) (s : R), shownW (unW s r).1 (unW s r).2 = r
  | [], _ => rfl
  | y :: r, s => by
      show (mu (unW y.1 r).1 (unW y.1 r).2, y.2) :: shownW (unW y.1 r).1 (unW y.1 r).2 = y :: r
      rw [mu_unW r y.1, shownW_unW r y.1]

/-! ## The map forth is additive -/

/-- Two lists of pairs, added entry by entry. -/
def addW (l l' : List (R × R)) : List (R × R) :=
  List.zipWith (fun x y => (x.1 + y.1, x.2 + y.2)) l l'

/-- The sum is additive, for lists of the same length. -/
theorem mu_addW : ∀ (l l' : List (R × R)) (c c' : R), l.length = l'.length →
    mu (addW l l') (c + c') = mu l c + mu l' c'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | x :: l, y :: l', c, c', h => by
      show (x.1 + y.1 + (x.2 + y.2)) + 2 * mu (addW l l') (c + c') = _
      rw [mu_addW l l' c c' (Nat.succ.inj h)]
      show _ = (x.1 + x.2 + 2 * mu l c) + (y.1 + y.2 + 2 * mu l' c')
      ring

/-- The rounds' pairs are additive, for lists of the same length. -/
theorem shownW_addW : ∀ (l l' : List (R × R)) (c c' : R), l.length = l'.length →
    shownW (addW l l') (c + c') = addW (shownW l c) (shownW l' c')
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _, _, h => by cases h
  | x :: l, y :: l', c, c', h => by
      show (mu (addW l l') (c + c'), x.2 + y.2) :: shownW (addW l l') (c + c') =
        (mu l c + mu l' c', x.2 + y.2) :: addW (shownW l c) (shownW l' c')
      rw [mu_addW l l' c c' (Nat.succ.inj h), shownW_addW l l' c c' (Nat.succ.inj h)]

/-- The coefficients with unW ds dr added. -/
def shiftW (l : List (R × R)) (c ds : R) (dr : List (R × R)) : List (R × R) × R :=
  (addW l (unW ds dr).1, c + (unW ds dr).2)

/-- Adding unW ds dr to the coefficients changes the sum by ds and the rounds' pairs by dr, if dr
has as many pairs as there are variables. -/
theorem shown_shiftW (l : List (R × R)) (c ds : R) (dr : List (R × R))
    (h : dr.length = l.length) :
    mu (shiftW l c ds dr).1 (shiftW l c ds dr).2 = mu l c + ds ∧
      shownW (shiftW l c ds dr).1 (shiftW l c ds dr).2 = addW (shownW l c) dr := by
  have hl : l.length = (unW ds dr).1.length := by rw [length_unW, h]
  constructor
  · show mu (addW l (unW ds dr).1) (c + (unW ds dr).2) = _
    rw [mu_addW l _ c _ hl, mu_unW]
  · show shownW (addW l (unW ds dr).1) (c + (unW ds dr).2) = _
    rw [shownW_addW l _ c _ hl, shownW_unW]

/-- An example over the integers. -/
theorem mu_two : mu [((1 : ℤ), 2)] 3 = 9 ∧ shownW [((1 : ℤ), 2)] 3 = [(3, 2)] ∧
    unW (9 : ℤ) [(3, 2)] = ([(1, 2)], 3) := by
  refine ⟨by decide, by decide, by decide⟩

/-- The same where 2 = 0: nothing is divided. -/
theorem mu_char_two : unW (mu [((1 : ZMod 2), 1)] 1) (shownW [((1 : ZMod 2), 1)] 1) =
    ([(1, 1)], 1) := unW_shown _ _

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.unW_shown
#print axioms OnBytes.LinkSim.mu_unW
#print axioms OnBytes.LinkSim.shownW_unW
#print axioms OnBytes.LinkSim.shown_shiftW
