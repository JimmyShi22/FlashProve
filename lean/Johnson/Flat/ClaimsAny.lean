-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ClaimsAny.lean: what the statements read of a decoded stored table, at any model
numbers P: the committed matrix of digits, the next token at the weights that the library's layout
reads off it, and the claim of an instance.

Definitions, and one equation. Johnson/Flat/Claims.lean gives an A : `D.Claims X` at the reference
numbers, through the index `Cm.Idx` and the relation `Cm.PaperTrue`,
which name these numbers outright. What lies below them takes the numbers as an argument: the layout
of the weights in a matrix of digits (`Inst.Model.Layout.weightsOf P k W`, `WFW P k W h`,
Inst/Model/Layout.lean) and the integer program on arrays (`IntegerTransformer.model`,
IntegerModel/Model.lean, at the arrays of IntegerModel/Readable/Exists.lean). This file builds an A
from these, so that there is one at the small example's numbers too (`sizesAt`,
Johnson/Flat/Instance.lean).

Main names:
  `nextOfDigits P k s W`: the next token after a list of tokens, at the weights that the layout
    reads off the matrix of digits W with 2 ^ k columns, at a table of scales s.
  `nextOfDigits_ppref`: at the reference numbers and an index i it is `IntegerModel.nextToken s
    i.index`.
  `digitsIn D N P M`: a well-formed matrix of digits that says the cells M, if there is one.
  `TrueBy next x`: the range of the instance x is not empty, and each checked token is what `next`
    gives after the tokens before it; the reply token is 0 if the range ends before the window's
    end.
  `claimsAt D N P s`: the A. Its claim is an implication, as that of `claims`
    (Johnson/Flat/Claims.lean): never to be laid as a relation without "in range" before it.
  `nextTokenIn D N P s`: the next token at the digits that M holds.
Limits: nothing is proved beside the equation. `digitsIn` picks by choice and cannot be run. AT
OTHER NUMBERS THAN THE REFERENCE's THE PROGRAM IS NOT THAT OF A PARAMETER FILE: the five fixed
tables are the library's own (the rotary tables at the reference's base, 2,307 rows of the
exponential), a table of scales has words for 48 layers, of which the first P.layers are read, and
the shifts that `sizesOf` leaves at the reference's values are not read by this program, which takes
them from s. SO AT THE SMALL EXAMPLE's SIZES THE HYPOTHESIS ON THE PROOF FILE's PROTOCOL CANNOT BE
MET BY THE SMALL EXAMPLE's PROTOCOL: its programs prove another program. That `nextOfDigits` ever
returns a token at these sizes is not shown. `TrueBy` asks the program's conditions on each prefix
up to the last covered position, not on the whole window. That `TrueBy` at the reference numbers is
`Cm.PaperTrue` is not shown here.

-/
import Johnson.Flat.Claims

set_option autoImplicit false

/- No default table of scales here: each table is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model VerifiableInference

/-- The next token after `tokens`, at the weights that the layout reads off the matrix of digits W.
AT OTHER SIZES THAN THE REFERENCE's THIS IS NOT THE PROGRAM OF A PARAMETER FILE (the head of this
file): a description made of it there type-checks, and no real protocol's soundness can be shown of
it. -/
def nextOfDigits (P : Params) (k : ℕ) (s : Cm.Scales) (W : Mat) (tokens : List Token) :
    Option Token :=
  IntegerTransformer.model (IntegerModel.Readable.settingsArrays P ⟨s.w, s.nf, AcceptancePolicy.exact⟩)
    (IntegerModel.Readable.tablesArrays P)
    (IntegerModel.Readable.weightsArrays P (Layout.weightsOf P k W)) tokens.toArray

/-- At the reference numbers and an index it is `IntegerModel.nextToken`. -/
theorem nextOfDigits_ppref (s : Cm.Scales) (i : Cm.Idx) (tokens : List Token) :
    nextOfDigits ppref Layout.kRef s i.mat tokens = IntegerModel.nextToken s i.index tokens := rfl

variable (D : DecR) (N : MatrixNums) (P : Params)

open Classical in
/-- A well-formed matrix of digits that says M, if there is one. -/
noncomputable def digitsIn (M : Cells D N) : Option Mat :=
  if h : ∃ W : Mat, Says D N M W ∧ Layout.WFW P (N.kLo + D.v) W N.rows then
    some (Classical.choose h)
  else none

/-- The tokens of the window before and at position t. -/
def upTo {P : Params} (x : Instance' P) (t : ℕ) : List Token := (List.range (t + 1)).map x.tok

/-- The instance is true by a function that gives the next token. -/
def TrueBy {P : Params} (next : List Token → Option Token) (x : Instance' P) : Prop :=
  (x.r < x.e ∧ x.e ≤ P.T) ∧ (∀ t, x.r ≤ t → t < x.e → next (upTo x t) = some (x.w t)) ∧
    (x.e < P.T → x.y.val = 0)

/-- **What the statements read of a decoded table**, at the model numbers P and a table of scales.
ITS CLAIM `Rel` IS AN IMPLICATION ("if the matrix holds digits, then ..."): never to be laid as a
configuration's relation without `inRange` before it; why: the docstring of `claims`
(Johnson/Flat/Claims.lean). AT OTHER SIZES THAN THE REFERENCE's THIS IS NOT THE PROGRAM OF A
PARAMETER FILE (the head of this file): a description made of it there type-checks, and no real
protocol's soundness can be shown of it. -/
noncomputable def claimsAt (s : Cm.Scales) : D.Claims (Instance' P) where
  Mat := Cells D N
  mat := cellsOf D N
  inRange := fun M => (digitsIn D N P M).isSome = true
  Rel := fun M x => ∀ W, digitsIn D N P M = some W → TrueBy (nextOfDigits P (N.kLo + D.v) s W) x
  mat_cut := cellsOf_cut D N

/-- The next token at the digits that M holds; `none` if it holds none. AT OTHER SIZES THAN THE
REFERENCE's THIS IS NOT THE PROGRAM OF A PARAMETER FILE (the head of this file): a description made
of it there type-checks, and no real protocol's soundness can be shown of it. -/
noncomputable def nextTokenIn (s : Cm.Scales) (M : Cells D N) (tokens : List Token) :
    Option Token :=
  (digitsIn D N P M).bind fun W => nextOfDigits P (N.kLo + D.v) s W tokens

end OnBytes.Flat
