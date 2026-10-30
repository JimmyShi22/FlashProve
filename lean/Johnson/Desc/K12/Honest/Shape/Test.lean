-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/Shape/Test.lean: THE SHAPE OF THE STRUCTURE INSIDE A PROXIMITY TEST (`T12`,
Johnson/Desc/K12/Join.lean): the core's shape (Johnson/Desc/Ground/Shape/Core.lean), the group's
number, the mask's number, and what is left of what passes from a part to the next when every field
element is left out. Types and the reader.

The types. None holds a field element.
  `ClaimSh`   behind a batching: lay : GroupLayout (whole) · group : Nat · kept : Nat (the NUMBER of
      kept forms) · d : Nat (the length of the vector on the mask table) · cFits, cPlain : Bool.
  `SingleSh`   behind a fold: code, maskCode : Nat · lay : GroupLayout · gamma : Nat (the NUMBER of
      challenges) · masks, fresh : Nat · kept : Nat · d : List Nat (each mask row's vector's
      length) · keptRows : Nat · cFits, cPlain : Bool.
  `SwitchedSh`   behind a switch: g : Nat · kept, others : List Nat · logN : Nat · draws : Nat (the
      NUMBER of sampled positions; the positions are left out).
  `PassSh`   nothing | claim | single, with the new group's number | switched, with that number.
  `TestSh`   core : CoreSh · g : Nat · pass : PassSh · mask : Option Nat.
  `GroupLayout` (OnBytes/Iop/Ground.lean) is taken as it lies: numbers, and arrays of numbers, of
  Bools and of options of numbers.

THE MARKS ON A FORM. The tensors of the form on the main table are not in the shape: their number
can hang on a value. What guards ask of all of them is held as two Bools that the reader computes:
  `cFits`    `Own.formFits` (Johnson/Desc/Own/Shapes.lean) at the table's index bits: behind a
      batching lay.k + lay.logEll, behind a fold lay.logEll.
  `cPlain`   no tensor of the form has a written-out factor (`PlainForm`,
      OnBytes/Slice/BlkFoldVec.lean).

Limits. Types and readers: nothing is said here of a part of the test. `cFits` reads, at a tensor
with a written-out factor, whether a pair is (1, 1): where `cPlain` is true it reads no element.
Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.Ground.Shape.Marks
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Ground.Sh

/-- No tensor of the form has a written-out factor: with code. -/
def formPlainB (f : Form) : Bool := f.tensors.all fun v => v.denseVars.isEmpty

theorem formPlainB_iff {f : Form} : formPlainB f = true ↔ PlainForm f := by
  unfold formPlainB PlainForm
  simp only [List.all_eq_true, List.isEmpty_iff]

/-- The one claim behind a batching. -/
structure ClaimSh where
  lay : GroupLayout
  group : Nat
  kept : Nat
  d : Nat
  cFits : Bool
  cPlain : Bool

/-- The single rows behind a fold. -/
structure SingleSh where
  code : Nat
  maskCode : Nat
  lay : GroupLayout
  gamma : Nat
  masks : Nat
  fresh : Nat
  kept : Nat
  d : List Nat
  keptRows : Nat
  cFits : Bool
  cPlain : Bool

/-- What a switch returned, without the sampled positions. -/
structure SwitchedSh where
  g : Nat
  kept : List Nat
  others : List Nat
  logN : Nat
  draws : Nat

inductive PassSh where
  | nothing
  | claim (c : ClaimSh)
  | single (r : SingleSh) (next : Nat)
  | switched (o : SwitchedSh) (next : Nat)

/-- **The shape of the structure inside a proximity test.** -/
structure TestSh where
  core : CoreSh
  g : Nat
  pass : PassSh
  mask : Option Nat

def claimSh (row : GroupRow) (L : GroupLayout) : ClaimSh :=
  ⟨L, row.group, row.kept.size, row.d.size, Own.formFits row.c (L.k + L.logEll), formPlainB row.c⟩

def singleSh (r : SingleRows) : SingleSh :=
  ⟨r.code, r.maskCode, r.layout, r.gamma.length, r.masks, r.fresh, r.kept.size,
    r.d.toList.map (·.size), r.keptRows, Own.formFits r.c r.layout.logEll, formPlainB r.c⟩

def switchedSh (o : Switched) : SwitchedSh :=
  ⟨o.g, o.kept.toList, o.others.toList, o.positions.logN, o.positions.draws.size⟩

def passSh : Passing → PassSh
  | .nothing => .nothing
  | .claim row L => .claim (claimSh row L)
  | .single rows n => .single (singleSh rows) n
  | .switched out _ n => .switched (switchedSh out) n

/-- **The reader.** -/
def testSh (t : T12) : TestSh := ⟨coreSh ⟨t.st, t.book, t.roots⟩, t.g, passSh t.pass, t.mask⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.formPlainB_iff
