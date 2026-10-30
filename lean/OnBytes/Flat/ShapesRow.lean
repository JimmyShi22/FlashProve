-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/ShapesRow.lean: the written shapes of stretches of a chain's rounds, one behind the
other, are the chain's written shape.

A chain of a file is written over `uLT C ds` (OnBytes/Maker/Trees.lean), ds the chain's list of
rounds' data. A reading block by block has, for each block, a written shape of its own, and appends
these from the left. If each block's shape is `uLT C` of a slice of ds, cut at given lengths, the
row of shapes is `uLT C ds`, as soon as the lengths add up to the length of ds or more. So the
equation of shapes is a comparison of two numbers. Definitions and proofs.

Main names:
  `uLT_append`: `uLT C (a ++ b) = uLT C a ++ uLT C b`.
  `cuts ns l`: l cut into slices of the lengths ns; `cuts_flatten`: one behind the other they are l,
    if `l.length ≤ ns.sum`.
  `rowSh C L`: the shapes of the lists L appended from the left; `rowSh_eq`: it is `uLT C
    L.flatten`.
  `row_cuts`: `rowSh C (cuts ns ds) = uLT C ds`, if `ds.length ≤ ns.sum`. The three chains of
    `chainsOf C D tF tJ t3` (OnBytes/Maker/Whole.lean) have the shapes `uLT C D.ds₁`, `uLT C D.ds₂`,
    `uLT C D.ds₃` by definition.
Limits: nothing on what a slice holds: that a block's rounds are the slice at its place is the
caller's choice, and what the block asks of its rounds is then asked of the slice. A last slice may
be shorter than its length says. No value is treated.
-/
import OnBytes.Maker.Whole

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Run Run.PQ OnBytes.Maker

theorem uLT_append (C : CK) : ∀ a b : List RDT, uLT C (a ++ b) = uLT C a ++ uLT C b
  | [], _ => rfl
  | d :: a, b => congrArg ((roundT C d).up :: ·) (uLT_append C a b)

/-- A list cut into slices of given lengths. -/
def cuts {α : Type} : List ℕ → List α → List (List α)
  | [], _ => []
  | n :: ns, l => l.take n :: cuts ns (l.drop n)

theorem cuts_flatten {α : Type} : ∀ (ns : List ℕ) (l : List α), l.length ≤ ns.sum →
    (cuts ns l).flatten = l
  | [], l, h => by
      have h0 : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 h)
      rw [h0]
      rfl
  | n :: ns, l, h => by
      have h1 : (l.drop n).length ≤ ns.sum := by
        rw [List.length_drop]
        rw [List.sum_cons] at h
        omega
      show l.take n ++ (cuts ns (l.drop n)).flatten = l
      rw [cuts_flatten ns (l.drop n) h1]
      exact List.take_append_drop n l

/-- The shapes of lists of rounds, appended from the left, behind a given shape. -/
def rowFrom (C : CK) : Shape → List (List RDT) → Shape
  | s, [] => s
  | s, l :: L => rowFrom C (s ++ uLT C l) L

/-- The shapes of lists of rounds, appended from the left. -/
def rowSh (C : CK) (L : List (List RDT)) : Shape := rowFrom C [] L

theorem rowFrom_eq (C : CK) : ∀ (a : List RDT) (L : List (List RDT)),
    rowFrom C (uLT C a) L = uLT C (a ++ L.flatten)
  | a, [] => by
      show uLT C a = uLT C (a ++ [])
      rw [List.append_nil]
  | a, l :: L => by
      show rowFrom C (uLT C a ++ uLT C l) L = uLT C (a ++ (l ++ L.flatten))
      rw [← uLT_append, rowFrom_eq C (a ++ l) L, List.append_assoc]

theorem rowSh_eq (C : CK) (L : List (List RDT)) : rowSh C L = uLT C L.flatten :=
  rowFrom_eq C [] L

/-- The row of the slices' shapes is the chain's shape. -/
theorem row_cuts (C : CK) (ns : List ℕ) (ds : List RDT) (h : ds.length ≤ ns.sum) :
    rowSh C (cuts ns ds) = uLT C ds := by
  rw [rowSh_eq, cuts_flatten ns ds h]

end OnBytes.Flat

#print axioms OnBytes.Flat.uLT_append
#print axioms OnBytes.Flat.row_cuts
