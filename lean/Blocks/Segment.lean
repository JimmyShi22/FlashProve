-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Segment.lean: the field relation of one segment of the model's computation.

Its data and the relation. Two definitions; no statement. (Words of this library: lean/GLOSSARY.md.)
 * `TraceSpec F X`: the data, for a field F and a type X of instances: a type of cells (a trace
   assigns an integer to each cell); the exponent β; a type of keys (looked-up values), each key a
   function of the instance, the entries of the matrix of weights and the trace, with values in F
   (meant: a polynomial in cells and weights); the lookup table of each key, a set in F; a type of
   further identities, functions of the same arguments.
 * `TraceSpec.RF T x W t`: the field relation: (1) every cell is below 2^β in absolute value, (2)
   every key is an entry of its table, (3) every identity has the value 0.
Used by the feed-forward segment's relation (`trace`, Inst/Model/FF/Trace.lean).
Limits: that keys and identities are polynomials is no clause of the structure. Nothing on a
protocol, a stage or the relations between stages.
-/
import Blocks.Stage

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-! ## The field relation of a segment -/

/-- The part of the field relation that belongs to one segment: the data. A trace assigns an integer
to each cell. X is the type of instances; the matrix of weights is given by its entries. -/
structure TraceSpec (F X : Type) where
  Cell : Type
  /-- every cell is below 2^β in absolute value -/
  β : ℕ
  Key : Type
  /-- the keys (meant: polynomials in cells and weights; see the head's Limits) -/
  key : X → (ℕ → ℕ → F) → (Cell → ℤ) → Key → F
  /-- the lookup table of each key -/
  table : Key → Set F
  Idn : Type
  /-- the further identities, which have to vanish (meant: polynomials in cells and weights; see the
  head's Limits) -/
  idn : X → (ℕ → ℕ → F) → (Cell → ℤ) → Idn → F

/-- The field relation: (1) every cell is small, (2) every key is an entry of its table, (3) every
identity holds. -/
def TraceSpec.RF {F X : Type} [Zero F] (T : TraceSpec F X) (x : X)
    (W : ℕ → ℕ → F) (t : T.Cell → ℤ) : Prop :=
  (∀ c, |t c| < 2 ^ T.β) ∧ (∀ k, T.key x W t k ∈ T.table k) ∧ ∀ j, T.idn x W t j = 0

end Blocks
