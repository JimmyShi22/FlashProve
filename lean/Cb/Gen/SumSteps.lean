-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/SumSteps.lean: for the sumcheck protocol: a polynomial summand written as a sequence of
steps of degree at most 2, and the quadratic constraints which say that given numbers are its
intermediate values and its value at one point. No protocol.

Definitions and statements; the proofs are in Cb/Gen/SumStepsProofs.lean.

Terms. A record (`Blocks.Ledger`, Blocks/Form.lean) holds two lists of claims on forms and the list
of the opened forms: linear rows (the value is 0), product rows (the value is a given combination
∑ c o_i o_j of products of two factor rows' values), and the factor rows, which are the opened
forms.

The summand of a sumcheck is a polynomial G in values Y_0, .., Y_(nc-1) (the multilinear extensions
of nc vector maps at a point). It is given in steps of degree at most 2:
      Y_(nc+l) = Q_l(Y_0, .., Y_(nc+l-1))   for l < na  (auxiliary steps),
      G = Q_na(Y_0, .., Y_(nc+na-1))   (the last step).
Here the point is fixed: the coefficients of a step are elements of the ring.

Main names:
  `Steps.Hold`, at a and aEnd: what the output rows of the sumcheck say of numbers a_j and aEnd.
    Every auxiliary a is its step at the a's, and aEnd is the last step at the a's.
  `Steps.ledger`, at A and fEnd: the same as a record of claims on forms (`Blocks.Ledger` is this
    library's rendering of the quadratic constraint predicate).
  The three statements, each with the premise `S.Tri`:
  `Spec.hold_vals`: the true values satisfy the rows (honest side), and agree with the given values
    on the first nc variables.
  `Spec.out_of_hold`, the backward step: numbers that satisfy the rows and are right on the first
    nc variables have aEnd = G.
  `Spec.ledger_true_iff`: the record is true at y exactly if the values of the forms satisfy the
    rows.

Declared difference to a print of this protocol's technical report (lean/CREDITS.md): there
the factor rows are those a_j that occur in a product; here all nc + na are on the list (a later
product check then opens all of them).

Terms: lean/GLOSSARY.md.
-/
import Blocks.Form

set_option autoImplicit false

namespace Cb
open Blocks

/-- A polynomial of degree at most 2 in the variables Y_0, Y_1, ..: constant term, linear terms (c,
j), quadratic terms (c, j, j'). -/
structure QStep (E : Type) where
  c0 : E
  lin : List (E × ℕ)
  quad : List (E × ℕ × ℕ)

/-- The steps of a summand at one point: step l for l < na is auxiliary, step na is the last. -/
structure Steps (E : Type) where
  nc : ℕ
  na : ℕ
  step : ℕ → QStep E

section
variable {E : Type} [CommRing E]

/-- ∑ c · Y_j over a list of terms (c, j). -/
def linSum (Y : ℕ → E) (ts : List (E × ℕ)) : E := (ts.map fun t => t.1 * Y t.2).sum

def QStep.eval (q : QStep E) (Y : ℕ → E) : E := q.c0 + linSum Y q.lin + termSum Y q.quad

omit [CommRing E] in
/-- The step names only variables below n. -/
def QStep.Below (q : QStep E) (n : ℕ) : Prop :=
  (∀ t ∈ q.lin, t.2 < n) ∧ ∀ t ∈ q.quad, t.2.1 < n ∧ t.2.2 < n

namespace Steps

omit [CommRing E] in
/-- Step l, for l ≤ na, names only variables below nc + l. -/
def Tri (S : Steps E) : Prop := ∀ l, l ≤ S.na → (S.step l).Below (S.nc + l)

/-- The values after the first l auxiliary steps. -/
def fill (S : Steps E) (Y0 : ℕ → E) : ℕ → ℕ → E
  | 0 => Y0
  | l + 1 => Function.update (fill S Y0 l) (S.nc + l) ((S.step l).eval (fill S Y0 l))

/-- The true values of all variables. -/
def vals (S : Steps E) (Y0 : ℕ → E) : ℕ → E := S.fill Y0 S.na

/-- The value of the summand. -/
def out (S : Steps E) (Y0 : ℕ → E) : E := (S.step S.na).eval (S.vals Y0)

/-- What the rows say (see the head). -/
def Hold (S : Steps E) (a : ℕ → E) (aEnd : E) : Prop :=
  (∀ l, l < S.na → a (S.nc + l) = (S.step l).eval a) ∧ aEnd = (S.step S.na).eval a

variable {N : Type}

/-- The product row of step l. -/
def rowForm (S : Steps E) (A : ℕ → Form N E) (fEnd : Form N E) (l : ℕ) : Form N E :=
  (if l < S.na then A (S.nc + l) else fEnd) - Form.const (S.step l).c0 -
    ((S.step l).lin.map fun t => t.1 • A t.2).sum

/-- The rows as a record of claims. -/
def ledger (S : Steps E) (A : ℕ → Form N E) (fEnd : Form N E) : Ledger N E :=
  ⟨[], (List.range (S.nc + S.na)).map A,
    (List.range (S.na + 1)).map fun l => (S.rowForm A fEnd l, (S.step l).quad)⟩

end Steps
end

namespace Spec

def hold_vals : Prop :=
  ∀ (E : Type) [CommRing E] (S : Steps E) (Y0 : ℕ → E),
    S.Tri → S.Hold (S.vals Y0) (S.out Y0) ∧ ∀ j, j < S.nc → S.vals Y0 j = Y0 j

def out_of_hold : Prop :=
  ∀ (E : Type) [CommRing E] (S : Steps E) (Y0 a : ℕ → E) (aEnd : E), S.Tri →
    (∀ j, j < S.nc → a j = Y0 j) → S.Hold a aEnd →
    aEnd = S.out Y0 ∧ ∀ j, j < S.nc + S.na → a j = S.vals Y0 j

def ledger_true_iff : Prop :=
  ∀ (E N : Type) [CommRing E] [Fintype N] (S : Steps E) (A : ℕ → Form N E)
      (fEnd : Form N E) (y : N → E),
    S.Tri → ((S.ledger A fEnd).True y ↔ S.Hold (fun j => Form.val y (A j)) (Form.val y fEnd))

end Spec
end Cb
