-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Base.lean: the ground of the law of the constraint (fold) in the linear claim's
shared rounds: the equation that (fold) stands for, and how "SPLIT" cuts a constraint in two.

Main definitions: eqK, rowsOn, omegaOf, uOf, FoldEq, FoldCatches (a proposition), onOmega, onU.
Main theorems: part_add, coefficient_addUnit, neg_one, split_coefficient, split_target.

What is not claimed. FoldCatches is a statement here; its proof is in
Johnson/Desc/K14/Law/Catches.lean. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Text
import Johnson.Desc.Means.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : Reading K)

/-- eq(z, j): the product over the coordinates of z, the lowest bit of j first. -/
def eqK : List K → Nat → K
  | [], _ => 1
  | x :: l, j => (if j % 2 = 1 then x else 1 - x) * eqK l (j / 2)

/-- The constraints on a group. -/
def rowsOn (d : St) (g : Nat) : List Row := ((d.st.groups[g]?).map (·.rows.toList)).getD []

/-- omega_col and u as the words hold them. -/
def omegaOf (l : Lin) (lay : VectorLay) (m : Words K) (j : Nat) : K :=
  m l.oOmega .main (lay.index j)

@[inherit_doc omegaOf]
def uOf (l : Lin) (m : Words K) (k : Nat) : K := m l.oU.oracle .main (l.oU.lay.index k)

/-- (fold) as an equation in K. -/
@[reducible] def FoldEq (S : LinShape) (psiLo z : List K) (omega u : Nat → K) : Prop :=
  (∑ j ∈ Finset.range S.matrixRows, eqK z j * omega j) =
    ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK psiLo t * eqK z j * u (t + 2 ^ S.kLo * j)

/-- **CATCHES**: over a finite field: if omega_col is not col_psi_lo(u) on M's rows, (fold) holds at
no more than kRow |K| ^ (kRow - 1) of the |K| ^ kRow points z_fd. -/
def FoldCatches [Fintype K] [DecidableEq K] : Prop :=
  ∀ (S : LinShape) (psiLo : List K) (omega u : Nat → K), S.matrixRows ≤ 2 ^ S.kRow →
    (∃ j < S.matrixRows,
      omega j ≠ ∑ t ∈ Finset.range (2 ^ S.kLo), eqK psiLo t * u (t + 2 ^ S.kLo * j)) →
    (Finset.univ.filter fun z : Fin S.kRow → K =>
      FoldEq S psiLo (List.ofFn z) omega u).card ≤ S.kRow * Fintype.card K ^ (S.kRow - 1)

/-! ## How "SPLIT" cuts a constraint in two -/

/-- A sum over a list, cut in two by a test. -/
theorem sum_cut {α : Type} (l : List α) (b : α → Bool) (f : α → K) :
    ((l.filter fun a => b a == true).map f).sum + ((l.filter fun a => b a == false).map f).sum =
      (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : b a
    · simp only [List.filter_cons, h, List.map_cons, List.sum_cons]
      simp only [Bool.false_eq_true, beq_self_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons, beq_iff_eq]
      rw [← ih]; ring
    · simp only [List.filter_cons, h, List.map_cons, List.sum_cons]
      simp only [Bool.true_eq_false, beq_self_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons, beq_iff_eq]
      rw [← ih]; ring

/-- The two parts of a constraint add up to it, entry by entry. -/
theorem part_add (row : Row) (members : Array Nat) (o : Nat) (pt : Part) (i : Nat) :
    ρ.val ((part row members true).coefficient o pt i) +
      ρ.val ((part row members false).coefficient o pt i) = ρ.val (row.coefficient o pt i) := by
  simp only [Row.coefficient_val, part, Array.toList_filter]
  rw [← sum_cut row.terms.toList (fun t => members.contains t.oracle),
    ← sum_cut row.units.toList (fun t => members.contains t.oracle),
    ← sum_cut row.runs.toList (fun t => members.contains t.oracle),
    ← sum_cut row.forms.toList (fun t => members.contains t.oracle)]
  ring

/-- A coefficient more on one entry. -/
theorem coefficient_addUnit (r : Row) (o' : Nat) (p' : Part) (i' : Nat) (c : E) (o : Nat)
    (pt : Part) (i : Nat) :
    ρ.val ((r.addUnit o' p' i' c).coefficient o pt i) =
      ρ.val (r.coefficient o pt i) + if o' = o ∧ p' = pt ∧ i' = i then ρ.val c else 0 := by
  simp only [Row.coefficient_val, Row.addUnit, Array.toList_push, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  by_cases h1 : o' = o <;> by_cases h2 : p' = pt <;> by_cases h3 : i' = i <;> simp [h1, h2, h3] <;>
    ring

/-- Every reading takes the program's -1 to -1. -/
theorem neg_one : ρ.val (negE oneE) = -1 := by
  have h : addE oneE (negE oneE) = zeroE := by decide
  have h2 := ρ.add oneE (negE oneE)
  rw [h, ρ.zero, ρ.one] at h2
  linear_combination -h2

/-- The two constraints that "SPLIT" makes of a constraint. -/
def onOmega (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E) : Row :=
  { (part row members true).addUnit oSp .mask kappa oneE with target := mu }

@[inherit_doc onOmega]
def onU (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E) : Row :=
  { (part row members false).addUnit oSp .mask kappa (negE oneE) with
    target := subE row.target mu }

/-- Entry by entry they add up to it: the mask's entry falls out. -/
theorem split_coefficient (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E) (o : Nat)
    (pt : Part) (i : Nat) :
    ρ.val ((onOmega row members oSp kappa mu).coefficient o pt i) +
      ρ.val ((onU row members oSp kappa mu).coefficient o pt i) =
        ρ.val (row.coefficient o pt i) := by
  have ha : (onOmega row members oSp kappa mu).coefficient o pt i =
      ((part row members true).addUnit oSp .mask kappa oneE).coefficient o pt i := rfl
  have hb : (onU row members oSp kappa mu).coefficient o pt i =
      ((part row members false).addUnit oSp .mask kappa (negE oneE)).coefficient o pt i := rfl
  rw [ha, hb, coefficient_addUnit, coefficient_addUnit, ← part_add ρ row members o pt i, ρ.one,
    neg_one]
  split <;> ring

/-- So do their targets. -/
theorem split_target (row : Row) (members : Array Nat) (oSp kappa : Nat) (mu : E) :
    ρ.val (onOmega row members oSp kappa mu).target + ρ.val (onU row members oSp kappa mu).target =
      ρ.val row.target := by
  show ρ.val mu + ρ.val (subE row.target mu) = ρ.val row.target
  rw [ρ.sub]; ring

end Desc.K14.Law
